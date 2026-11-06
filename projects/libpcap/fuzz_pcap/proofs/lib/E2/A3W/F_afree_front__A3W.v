(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecSlog__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3 F_aunwind.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc1b__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_s__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_adrain__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require NDestr.
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_tail.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_afree_front.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecSlog__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3 F_aunwind. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc1b__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_s__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_adrain__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aunwind OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc1b__A3W.F_aunwind2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_afree_s OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_aintal OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_afree_iseg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc__A3W.F_adealloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_aqchunk.
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
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.
(* [comment removed for export] *)
Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6303744 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} {tlsI : ABase.atlsT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6303744 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (sclr_int a n H G1 G2) 4%nat; intros k A B C; nd_post); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (iclr_int a n H G2) 5%nat; intros k A B C D; nd_post); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>      (* [comment removed for export] *)
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (iclr_int a n H G2) 5%nat; intros k A B C D; nd_post); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.


Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section WithDepot.
Variable DI : ADepotIface.

(* [comment removed for export] *)
Notation front_W L sp t hm :=
  ([(bv_unsigned sp - 4096, bv_unsigned sp); (0xaf800, 0xaf800 + 0x81030); (0x13e088, 0x13e088 + 4);
    (t + 3168, t + 3169); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z) (only parsing).

Definition free_front_post (L : alayout) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t hm n b1 actx lo : Z) (trt : list Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (id : Z) (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) m' (sj' tb' : list word) (junk2 : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x5632c) (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp t0 t1 t2
                  sp (Z_to_bv 64 (hm + 16))
                  (Z_to_bv 64 0xab270) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 (t + 208)) (Z_to_bv 64 (bv_unsigned sp + -2128))
                  (Z_to_bv 64 hm) (Z_to_bv 64 n) a6 a7
                  (Z_to_bv 64 0x562bc) (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 (bv_unsigned sp + -81))
                  s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x37ff4) fc None m' (seg_rom asegs)
    /\ munch (front_W L sp t hm) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -2128)
    /\ 0 < id < 2^31
    /\ rw_cells asegs m' hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)]
    /\ rw_cells asegs m' (hm + 16) [C8 (Z_to_bv 64 id)]
    /\ u64arr asegs m' (t + 2800) sj' /\ length sj' = 46%nat
    /\ rw_cells asegs m' (t + 3168) [C1 (Z_to_bv 8 0)]
    /\ rw_cells asegs m' 0x13e088 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ stk asegs m' 0xaf800 (0xaf800 + 0x81030)
    /\ (forall j, 0 <= j < 32768 -> bytes_at asegs m' (0xaf808 + 8 * j) (le8 (Z_to_bv 64 0)))
    (* [comment removed for export] *)
    /\ rw_cells asegs m' (bv_unsigned sp + -2128) [C8 (Z_to_bv 64 (bv_unsigned sp + -2128 + 16)); C4 (Z_to_bv 64 (1 + Z.of_nat (length trt))); C4 (Z_to_bv 64 0)]
    /\ u64arr asegs m' (bv_unsigned sp + -2128 + 16) tb' /\ length tb' = 255%nat
    /\ rw_cells asegs m' (bv_unsigned sp + -72) [C8 sp; CB 8 junk2; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ ADEPOT DI L m'.

Definition free_front_spec__stmt : Prop := forall (L : alayout) (ia : bool) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem)
    (t ctx hm n b1 actx lo top bot : Z) (uw : word) (sj : list word) (trt : list Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 (hm + 16) ->
  bv_unsigned sp mod 16 = 0 ->
  (* [comment removed for export] *)
  allocA_cells m ctx t ->
  rw_cells asegs m 0xa54a0 [C8 (Z_to_bv 64 0x140128); C8 (Z_to_bv 64 0xabdf8); C8 (Z_to_bv 64 0xae5f8);
                             C8 (Z_to_bv 64 0xaf2e8); C8 (Z_to_bv 64 0xaf2f0); C8 (Z_to_bv 64 0xaf2e0)] ->
  rw_cells asegs m 0xaf2fc [C4 (Z_to_bv 64 30)] ->
  rw_cells asegs m 0x14014a [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m 0xa5490 [C8 (Z_to_bv 64 0x13e0a0)] -> rw_cells asegs m 0x13e0a0 [C8 (Z_to_bv 64 4096)] ->
  rw_cells asegs m 0x1400c8 [C8 (Z_to_bv 64 0)] ->
  (* [comment removed for export] *)
  rw_cells asegs m 0x13e088 [C1 (Z_to_bv 8 (if ia then 1 else 0)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  stk asegs m 0xaf800 (0xaf800 + 0x81030) ->
  (ia = true -> forall j, 0 <= j < 32768 -> bytes_at asegs m (0xaf808 + 8 * j) (le8 (Z_to_bv 64 0))) ->
  (* [comment removed for export] *)
  rw_cells asegs m (ctx + 8) [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m t [C8 (Z_to_bv 64 ctx); C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)] ->
  rw_cells asegs m (t + 40) [C1 (Z_to_bv 8 0)] -> rw_cells asegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  0 < ctx -> AIMG_HI <= ctx -> ctx + 4096 <= ATOP ->
  iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  (* [comment removed for export] *)
  rw_cells asegs m hm [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  rw_cells asegs m (hm + 16) [C8 uw] -> 0 <= b1 < 256 -> Z.land b1 3 = 1 -> 0 <= n < 2^32 -> hm mod 16 = 0 ->
  ablk hm (hm + 16 + rup n 8) -> tclr hm 24 -> hm + 24 <= ATOP ->      (* [comment removed for export] *)
  (hm + 24 <= t \/ t + 4096 <= hm) -> (hm + 24 <= ctx \/ ctx + 4096 <= hm) ->
  (* [comment removed for export] *)
  ADEPOT DI L m ->
  AIMG_HI <= al_nodes L -> al_nodes L + 1048576 <= ATOP -> AIMG_HI <= al_store L -> al_store L + 8388608 <= ATOP ->
  (hm + 24 <= al_nodes L \/ al_nodes L + 1048576 <= hm) -> (hm + 24 <= al_store L \/ al_store L + 8388608 <= hm) ->
  (t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) -> (t + 4096 <= al_store L \/ al_store L + 8388608 <= t) ->
  (ctx + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= ctx) -> (ctx + 4096 <= al_store L \/ al_store L + 8388608 <= ctx) -> tclr (al_nodes L) 1048576 -> tclr (al_store L) 8388608 ->
  (* [comment removed for export] *)
  afree_unw RNG lo m top sp s0 ra trt ->
  bv_unsigned s0 <> bv_unsigned sp + 8 ->
  In (AFREE_PC :: trt) (al_U L) ->
  0 <= bot -> bot < bv_unsigned sp -> bot < top -> 4096 <= top <= 2^47 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 -> rng RNG hm 24 ->
  evtF asegs RNG (free_front_post L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n b1 actx lo trt m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 0).
Variable ia : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 1).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 2).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 3).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 4).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 5).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 6).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 7).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 8).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 9).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 10).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 11).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 12).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 13).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 14).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 15).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 16).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 17).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 18).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 19).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 20).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 21).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 22).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 23).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 24).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 25).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 26).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 27).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 28).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 29).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 30).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 31).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 32).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 33).
Variable F : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 34).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 35).
Variable m : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 36).
Variable t : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 37).
Variable ctx : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 38).
Variable hm : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 39).
Variable n : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 40).
Variable b1 : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 41).
Variable actx : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 42).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 43).
Variable top : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 44).
Variable bot : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 45).
Variable uw : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 46).
Variable sj : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 47).
Variable trt : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 48).
#[using="Type"] Lemma free_front_spec__body : ltac:(let T := type of (fun (h : free_front_spec__stmt) => h L ia RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m t ctx hm n b1 actx lo top bot uw sj trt) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (ia, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (t, (ctx, (hm, (n, (b1, (actx, (lo, (top, (bot, (uw, (sj, trt))))))))))))))))))))))))))))))))))))))))))))))))) as _.

  intros ST CEIL LO MI TP Ha0 SP16 AC GOT6 MCS CF34 GPG PGC HK FL IAS IAM CT8 TT0 SW UW STATS LSJ CX0 C0 C1 T0 T1 CT2
         HD HUW B1 B13 NR AL HLO TCH HHI DHT DHC DEP N0 N1 R0 R1 DHN DHS DTN DTS DCN DCS XTNO XTST
         UNW S0NE TRU B0 BB BOTOP TOP RA4 RANE RIMG RTLS RSTK RCTX RT RNO RST RH. band_lin.   (* [comment removed for export] *)
  (pose proof (ablk_lin _ _ HLO) as ndP__; nd_pre ndP__ 4%nat; intros HL1 HL2 HL3 HL4; nd_post). unfold AIMG_HI in HL1. band_int HLO.   (* [comment removed for export] *)
  tclr_int TCH.      (* [comment removed for export] *)
  pose proof (afree_unw_length _ _ _ _ _ _ _ _ UNW) as LTRT.
  pose proof (afree_unw_sp47 _ _ _ _ _ _ _ _ UNW ltac:(clear -TOP; lia)) as SP47.
  pose proof AC as AC'. (nd_pre AC' 8%nat; intros INI RSS IMAX TI TK T88 TSD CT; nd_post).
  unfold AIMG_HI, AINSTANCE, ATP88, ATSD, ATSDI, ATSDK, AINITED, ARSSLIM, GOT_PGSZ, APGSZ, AFREE_SYM, AFREE_PC in *.
  word_range sp SPR. word_range s0 S0R. word_range ra RAR.
  box DHT. box DHC. box DHN. box DHS. box DTN. box DTS. box DCN. box DCS. box CT2.
  pose proof TT0 as TTx. rw_split TTx 1%nat TTc TT. clear TTc.
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (ficptA_spec (hm + 16) ia RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo);
      try eassumption; try (unfold AIA_FLAG, AIA_BASE, AIA_SIZE, AIA_MAP1; lia).
    all: try lazymatch goal with
         | |- rw_cells _ _ AIA_FLAG _ => exact FL
         | |- stk _ _ AIA_BASE _ => exact IAS
         | |- _ = true -> _ => exact IAM
         | |- rng _ _ _ => solve_rng
         end.
    all: match goal with |- ?G => idtac "REMA" G end. }
  cbv beta. intros ms1 PA. unfold ficptA_post in PA.
  (nd_pre PA 13%nat; intros t0a t1a t2a a6a a7a t3a t4a t5a t6a m1 junk1 junk2 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 10%nat; intros MUa WMa MIa STa FRA FRt FRs FL1 IAS1 IAM1; nd_post).
  (* [comment removed for export] *)
  pose proof FRs as FRs0. rw_split FRs0 7%nat FRsx FRsr. clear FRsx.
  destruct FRsr as [[_ BSR] _]. cbn [cells_bytes cbytes app] in BSR. rewrite app_nil_r in BSR.
  apply bytes_at_app in BSR. destruct BSR as [BS0 BRA]. rewrite length_le8 in BRA.
  replace (bv_unsigned sp + -16 + Z.of_nat 8) with (bv_unsigned sp - 8) in BRA by lia.
  replace (bv_unsigned sp + -16) with (bv_unsigned sp - 16) in BS0 by lia.
  assert (UC1 : forall tr, trt = bv_unsigned ra :: tr -> uchain m top 352956 (bv_unsigned sp) (bv_unsigned s0) 28%nat tr -> bv_unsigned sp + 16 < top ->
                uchain m1 top 352956 bot (bv_unsigned sp) 29%nat ([bv_unsigned ra] ++ tr)).
  { intros tr _ UC BTX. replace ([bv_unsigned ra] ++ tr) with ((if bv_unsigned ra =? 352956 then [] else [bv_unsigned ra]) ++ tr)
      by (replace (bv_unsigned ra =? 352956) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
    eapply (uc_step m1 top 352956 bot (bv_unsigned sp) 29%nat (bv_unsigned s0) (bv_unsigned ra) tr); try lia.
    - rewrite Z_to_bv_bv_unsigned. exact BS0.
    - rewrite Z_to_bv_bv_unsigned. exact BRA.
    - replace (bv_unsigned ra =? 352956) with false by (symmetry; apply Z.eqb_neq; lia). cbn [Nat.pred].
      destruct (Z_le_gt_dec (bv_unsigned sp + 16) (bv_unsigned s0)) as [GE|LT].
      + eapply uchain_frame; [exact UC|]. intros a Ha. apply MUa. cbn [outside]. rewrite unsigned_lit by lia. lia.
      + inversion UC; subst; [apply uc_stop; assumption | exfalso | exfalso]; Z.div_mod_to_equations; lia. }
  clear BS0 BRA.
  (* [comment removed for export] *)
  xport TI MUa WMa ltac:(lia). xport TK MUa WMa ltac:(lia). xport T88 MUa WMa ltac:(lia). xport TSD MUa WMa ltac:(lia).
  xport CT MUa WMa ltac:(lia). xport GPG MUa WMa ltac:(lia). xport PGC MUa WMa ltac:(lia). xport TT MUa WMa ltac:(lia).
  xport TT0 MUa WMa ltac:(lia). xport CT8 MUa WMa ltac:(lia).
  xport SW MUa WMa ltac:(lia). xport UW MUa WMa ltac:(lia). xport INI MUa WMa ltac:(lia).
  xport HD MUa WMa ltac:(lia). xport HUW MUa WMa ltac:(lia). xport HK MUa WMa ltac:(lia). xport STATS MUa WMa ltac:(rewrite LSJ; lia).
  assert (DEP1 : ADEPOT DI L m1).
  { eapply (adi_frame DI); [exact DEP | exact MUa | exact WMa |].
    repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq; lia|]). apply Forall_nil. }
  clear DEP.
  pose proof FRA as FRA0. rw_split FRA0 1%nat FRp FRz. rw_split FRz 1%nat SZC TAG.
  change 2040%nat with (8 * 255)%nat in FRt. destruct (u64arr_of_CB _ _ 255%nat _ FRt) as [TB LTB].
  pose proof FRs as FRs1. rw_split FRs1 1%nat BPJ REST.
  replace (bv_unsigned sp + -2120) with (bv_unsigned sp + -2128 + 8) in SZC by lia.
  replace (bv_unsigned sp + -2112) with (bv_unsigned sp + -2128 + 16) in TB by lia.
  replace (bv_unsigned sp + -72) with (bv_unsigned sp + -2128 + 2056) in BPJ by lia.
  (* [comment removed for export] *)
  step.                                                          (* [comment removed for export] *)
  name_sp sp (-2128).
  eapply evtF_cut with (P := unwind_impl_post (bv_unsigned sp + -2128) 352956 (bv_unsigned sp) t _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc lo trt m1).
  { destruct UNW as [(tr & Etr & UC & LTR & BTX & RTOP)|(Etr & TOPLE & SPLT)]; rewrite Etr.
    - eapply (unwind_impl_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (bv_unsigned sp + -2128) 352956 (bv_unsigned sp) ctx t top bot lo (words_of_bytes junk1) ([bv_unsigned ra] ++ tr)).
      all: try lazymatch goal with
         | |- stk _ _ _ _ => rewrite Hsp; exact STa
         | |- mem_inv _ _ => exact MIa
         | |- @eq word _ _ => rewrite ?Esp; first [reflexivity | exact TP | rewrite Z_to_bv_bv_unsigned; reflexivity | apply Z_to_bv_eqm; rewrite ?unsigned_lit by lia; lia]
         | |- ex _ => first [eexists; exact SZC | eexists; exact BPJ]
         | |- u64arr _ _ _ _ => exact TB
         | |- uchain _ _ _ _ _ _ _ => exact (UC1 tr Etr UC BTX)
         | |- _ \/ _ => unboxed CT2
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ (_ + 152) _ => exact CT
         | |- rw_cells _ _ (_ + 8) [C8 _; C8 _] => exact TT
         | |- rw_cells _ _ (_ + 40) _ => exact SW
         | |- rw_cells _ _ (_ + 3168) _ => exact UW
         end.
      all: try eassumption. all: try (unfold AIMG_HI; lia). all: try (Z.div_mod_to_equations; lia).
      all: match goal with |- ?G => idtac "REMU" G end.
    - eapply (unwind_impl_spec0 RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (bv_unsigned sp + -2128) 352956 (bv_unsigned sp) ctx t top bot lo (words_of_bytes junk1)).
      all: try lazymatch goal with
         | |- stk _ _ _ _ => rewrite Hsp; exact STa
         | |- mem_inv _ _ => exact MIa
         | |- @eq word _ _ => rewrite ?Esp; first [reflexivity | exact TP | rewrite Z_to_bv_bv_unsigned; reflexivity | apply Z_to_bv_eqm; rewrite ?unsigned_lit by lia; lia]
         | |- ex _ => first [eexists; exact SZC | eexists; exact BPJ]
         | |- u64arr _ _ _ _ => exact TB
         | |- _ \/ _ => unboxed CT2
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ (_ + 152) _ => exact CT
         | |- rw_cells _ _ (_ + 8) [C8 _; C8 _] => exact TT
         | |- rw_cells _ _ (_ + 40) _ => exact SW
         | |- rw_cells _ _ (_ + 3168) _ => exact UW
         end.
      all: try eassumption. all: try (unfold AIMG_HI; lia). all: try (Z.div_mod_to_equations; lia).
      all: match goal with |- ?G => idtac "REMU0" G end. }
  cbv beta. intros ms2 PU. unfold unwind_impl_post in PU.
  (nd_pre PU 18%nat; intros t0b t1b t2b a0b a1b a2b a3b a4b a5b a6b a7b t3b t4b t5b t6b m2 tb2 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 10%nat; intros MUu WMu MIu STu SZ2 TB2 LTB2 TRF2 BP2 UW2; nd_post).
  unname_sp. rewrite ?unsigned_lit in MUu by lia. rewrite ?unsigned_lit in STu by lia.
  replace (ret_pc (Z_to_bv 64 353048)) with (Z_to_bv 64 353048) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  (* [comment removed for export] *)
  assert (MU12 : munch [(bv_unsigned sp - 2288, bv_unsigned sp - 2128); (bv_unsigned sp - 2120, bv_unsigned sp - 2116); (bv_unsigned sp - 2112, bv_unsigned sp - 64); (t + 3168, t + 3169)]%Z m1 m2).
  { eapply munch_weaken; [| exact MUu]. unfold sub_fp; cbn [outside]; intros q Hq; lia. }
  xport TI MU12 WMu ltac:(lia). xport TK MU12 WMu ltac:(lia). xport T88 MU12 WMu ltac:(lia).
  xport TSD MU12 WMu ltac:(lia). xport CT MU12 WMu ltac:(ub CT2; ylia). xport CT8 MU12 WMu ltac:(ub CT2; ylia). xport TT0 MU12 WMu ltac:(lia).
  xport FRp MU12 WMu ltac:(lia). xport TAG MU12 WMu ltac:(lia). xport REST MU12 WMu ltac:(lia).
  xport HD MU12 WMu ltac:(ub DHT; ylia). xport HUW MU12 WMu ltac:(ub DHT; ylia). xport HK MU12 WMu ltac:(lia).
  xport STATS MU12 WMu ltac:(rewrite LSJ; lia).
  xport FL1 MU12 WMu ltac:(lia). xport IAS1 MU12 WMu ltac:(lia).
  assert (IAM2 : forall j, 0 <= j < 32768 -> bytes_at asegs m2 (0xaf808 + 8 * j) (le8 (Z_to_bv 64 0))).
  { intros j Hj. eapply bytes_at_agree; [exact (IAM1 j Hj)|].
    intros i Hi. apply MU12. cbn [outside]. rewrite length_le8 in Hi. rewrite wa_unsigned by lia. lia. }
  clear IAM1.
  assert (DEP2 : ADEPOT DI L m2).
  { eapply (adi_frame DI); [exact DEP1 | exact MU12 | exact WMu |].
    repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq; ub DTN; ub DTS; ylia|]). apply Forall_nil. }
  clear DEP1.
  (* [comment removed for export] *)
  rw_join SZ2 TAG SZT. rw_join FRp SZT SS.
  replace (bv_unsigned sp + -2112) with (bv_unsigned sp + -2128 + 16) in SS by lia.
  rewrite Z_to_bv_bv_unsigned in BP2. rw_join BP2 REST FRS.
  replace (bv_unsigned sp + -2128 + 2056) with (bv_unsigned sp + -72) in FRS by lia.
  (* [comment removed for export] *)
  zstep. zstep. step. step.                                      (* [comment removed for export] *)
  step.                                                          (* [comment removed for export] *)
  name_sp sp (-2128).
  eapply evtF_cut.
  { eapply (dealloc_spec t hm (bv_unsigned sp + -2128) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 n b1 actx ctx lo uw sj).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => rewrite Hsp; exact STu
         | |- mem_inv _ _ => exact MIu
         | |- @eq word _ _ => rewrite ?Esp; first [reflexivity | exact TP | apply Z_to_bv_eqm; rewrite ?unsigned_lit by lia; lia]
         | |- u64arr _ _ _ _ => exact STATS
         | |- _ \/ _ => first [unboxed DHT | unboxed DHC | unboxed CT2]
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ (_ + 152) _ => exact CT
         | |- rw_cells _ _ (_ + 16) _ => exact HUW
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD
         | |- rw_cells _ _ AFHOOK _ => exact HK
         end.
    all: try eassumption. all: try (unfold AIMG_HI; lia).
    all: match goal with |- ?G => idtac "REMD" G end. }
  cbv beta. intros ms3 PD. unfold dealloc_post in PD.
  (nd_pre PD 14%nat; intros t0c t1c t2c a4c a5c a6c a7c t3c t4c t5c t6c m3 sj3 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 8%nat; intros MUd WMd MId STd HD3 FC3 STATS3 LSJ3; nd_post).
  unname_sp. rewrite ?unsigned_lit in MUd by lia. rewrite ?unsigned_lit in STd by lia.
  (* [comment removed for export] *)
  xport TI MUd WMd ltac:(lia). xport TK MUd WMd ltac:(lia). xport T88 MUd WMd ltac:(lia). xport TSD MUd WMd ltac:(lia).
  xport CT MUd WMd ltac:(ub DHC; ub CT2; ylia). xport CT8 MUd WMd ltac:(ub DHC; ub CT2; ylia). xport TT0 MUd WMd ltac:(ub DHT; ylia).
  xport SS MUd WMd ltac:(lia). xport TB2 MUd WMd ltac:(rewrite LTB2; lia). xport FRS MUd WMd ltac:(lia).
  xport UW2 MUd WMd ltac:(ub DHT; ylia). xport FL1 MUd WMd ltac:(lia). xport IAS1 MUd WMd ltac:(lia).
  assert (IAM3 : forall j, 0 <= j < 32768 -> bytes_at asegs m3 (0xaf808 + 8 * j) (le8 (Z_to_bv 64 0))).
  { intros j Hj. eapply bytes_at_agree; [exact (IAM2 j Hj)|].
    intros i Hi. apply MUd. cbn [outside]. rewrite length_le8 in Hi. rewrite wa_unsigned by lia. lia. }
  clear IAM2.
  assert (DEP3 : ADEPOT DI L m3).
  { eapply (adi_frame DI); [exact DEP2 | exact MUd | exact WMd |].
    repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq; ub DTN; ub DTS; ub DHN; ub DHS; ylia|]). apply Forall_nil. }
  clear DEP2.
  (* [comment removed for export] *)
  name_sp sp (-2128).
  eapply evtF_cut.
  { eapply (qchunk_spec DI L t hm (bv_unsigned sp + -2128) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m3 n ctx b1 actx lo
              (1 + Z.of_nat (length trt)) 352956 (Z_to_bv 64 18446744069414584320) (Z_to_bv 64 top) (Z_to_bv 64 bot) tb2 trt).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => rewrite Hsp; exact STd
         | |- mem_inv _ _ => exact MId
         | |- ADEPOT _ _ _ => exact DEP3
         | |- @eq word _ _ => rewrite ?Esp; first [reflexivity | exact TP | apply Z_to_bv_eqm; rewrite ?unsigned_lit by lia; lia]
         | |- u64arr _ _ _ _ => exact TB2
         | |- In _ _ => exact TRU
         | |- map _ _ = _ => exact TRF2
         | |- _ \/ _ => first [unboxed DHN | unboxed DHS | unboxed DHT | unboxed DHC | unboxed DTN | unboxed DTS | unboxed DCN | unboxed DCS | unboxed CT2]
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ (_ + 152) _ => exact CT
         | |- rw_cells _ _ (_ + 8) _ => exact CT8
         | |- rw_cells _ _ (_ + 16) _ => exact FC3
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD3
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _] => exact TT0
         | |- rw_cells _ _ (_ + -2128) _ => exact SS
         end.
    all: try eassumption. all: try (unfold AIMG_HI; cbn [length]; lia).
    all: match goal with |- ?G => idtac "REMQ" G end. }
  cbv beta. intros ms4 PQ. unfold qchunk_post in PQ.
  (nd_pre PQ 12%nat; intros id t0d t1d t2d a6d a7d t3d t4d t5d t6d m4 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 7%nat; intros MUq WMq MIq STq FC4 IDR DEP4; nd_post).
  unname_sp. rewrite ?unsigned_lit in MUq by lia. rewrite ?unsigned_lit in STq by lia.
  (* [comment removed for export] *)
  xport HD3 MUq WMq ltac:(ub DHN; ub DHS; ylia). xport STATS3 MUq WMq ltac:(rewrite LSJ3; ub DHT; ub DTN; ub DTS; ylia).
  xport UW2 MUq WMq ltac:(ub DHT; ub DTN; ub DTS; ylia). xport FL1 MUq WMq ltac:(lia). xport IAS1 MUq WMq ltac:(lia).
  xport SS MUq WMq ltac:(lia). xport TB2 MUq WMq ltac:(rewrite LTB2; lia). xport FRS MUq WMq ltac:(lia).
  assert (IAM4 : forall j, 0 <= j < 32768 -> bytes_at asegs m4 (0xaf808 + 8 * j) (le8 (Z_to_bv 64 0))).
  { intros j Hj. eapply bytes_at_agree; [exact (IAM3 j Hj)|].
    intros i Hi. apply MUq. cbn [outside]. rewrite length_le8 in Hi. rewrite wa_unsigned by lia. lia. }
  clear IAM3.
  assert (MU : munch (front_W L sp t hm) m m4).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUq]].
    eapply munch_trans; [| eapply munch_weaken; [| exact MUd]].
    eapply munch_trans; [| eapply munch_weaken; [| exact MUu]].
    eapply munch_weaken; [| exact MUa].
    all: unfold sub_fp; cbn [outside]; intros q Hq; lia. }
  assert (WM : wmono asegs m m4).
  { eapply wmono_trans; [exact WMa|]. eapply wmono_trans; [exact WMu|]. eapply wmono_trans; [exact WMd| exact WMq]. }
  apply evtF_done. unfold free_front_post.
  exists id. do 9 eexists. exists m4, sj3, tb2, junk2.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MIq|]. split; [exact STq|]. split; [exact IDR|].
  split; [exact HD3|]. split; [exact FC4|]. split; [exact STATS3|]. split; [exact LSJ3|]. split; [exact UW2|].
  split; [exact FL1|]. split; [exact IAS1|]. split; [exact IAM4|].
  split; [exact SS|]. split; [exact TB2|]. split; [exact LTB2|].
  split; [exact FRS|]. exact DEP4.
  Unshelve. all: try exact STa; try exact STu; try exact STd.
Qed.
End Zd1.
#[using="Type"] Lemma free_front_spec : ltac:(let t := eval cbv delta [free_front_spec__stmt] in free_front_spec__stmt in exact t).
Proof. exact free_front_spec__body. Qed.
End WithDepot.
End CANSEC1.

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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aunwind.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc1b__A3W.F_aunwind2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_afree_s.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_aintal.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_afree_iseg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc__A3W.F_adealloc.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_aqchunk.TwB.
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
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.
(* [comment removed for export] *)
Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6307840 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6307840 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (sclr_int a n H G1 G2) 4%nat; intros k A B C; nd_post); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (iclr_int a n H G2) 5%nat; intros k A B C D; nd_post); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>      (* [comment removed for export] *)
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (iclr_int a n H G2) 5%nat; intros k A B C D; nd_post); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.


Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section WithDepot.
Variable DI : ADepotIface.

(* [comment removed for export] *)
Notation front_W L sp t hm :=
  ([(bv_unsigned sp - 4096, bv_unsigned sp); (0xafc00, 0xafc00 + 0x81030); (0x13e488, 0x13e488 + 4);
    (t + 3168, t + 3169); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z) (only parsing).

Definition free_front_post (L : alayout) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t hm n b1 actx lo : Z) (trt : list Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (id : Z) (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) m' (sj' tb' : list word) (junk2 : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x56394) (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp t0 t1 t2
                  sp (Z_to_bv 64 (hm + 16))
                  (Z_to_bv 64 0xab670) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 (t + 208)) (Z_to_bv 64 (bv_unsigned sp + -2128))
                  (Z_to_bv 64 hm) (Z_to_bv 64 n) a6 a7
                  (Z_to_bv 64 0x56324) (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 (bv_unsigned sp + -81))
                  s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x3805c) fc None m' (seg_rom asegs)
    /\ munch (front_W L sp t hm) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -2128)
    /\ 0 < id < 2^31
    /\ rw_cells asegs m' hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)]
    /\ rw_cells asegs m' (hm + 16) [C8 (Z_to_bv 64 id)]
    /\ u64arr asegs m' (t + 2800) sj' /\ length sj' = 46%nat
    /\ rw_cells asegs m' (t + 3168) [C1 (Z_to_bv 8 0)]
    /\ rw_cells asegs m' 0x13e488 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ stk asegs m' 0xafc00 (0xafc00 + 0x81030)
    /\ (forall j, 0 <= j < 32768 -> bytes_at asegs m' (0xafc08 + 8 * j) (le8 (Z_to_bv 64 0)))
    (* [comment removed for export] *)
    /\ rw_cells asegs m' (bv_unsigned sp + -2128) [C8 (Z_to_bv 64 (bv_unsigned sp + -2128 + 16)); C4 (Z_to_bv 64 (1 + Z.of_nat (length trt))); C4 (Z_to_bv 64 0)]
    /\ u64arr asegs m' (bv_unsigned sp + -2128 + 16) tb' /\ length tb' = 255%nat
    /\ rw_cells asegs m' (bv_unsigned sp + -72) [C8 sp; CB 8 junk2; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ ADEPOT DI L m'.

Definition free_front_spec__stmt : Prop := forall (L : alayout) (ia : bool) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem)
    (t ctx hm n b1 actx lo top bot : Z) (uw : word) (sj : list word) (trt : list Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 (hm + 16) ->
  bv_unsigned sp mod 16 = 0 ->
  (* [comment removed for export] *)
  allocA_cells m ctx t ->
  rw_cells asegs m 0xa5880 [C8 (Z_to_bv 64 0x140528); C8 (Z_to_bv 64 0xac1f8); C8 (Z_to_bv 64 0xae9f8);
                             C8 (Z_to_bv 64 0xaf6e8); C8 (Z_to_bv 64 0xaf6f0); C8 (Z_to_bv 64 0xaf6e0)] ->
  rw_cells asegs m 0xaf6fc [C4 (Z_to_bv 64 30)] ->
  rw_cells asegs m 0x14054a [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m 0xa5870 [C8 (Z_to_bv 64 0x13e4a0)] -> rw_cells asegs m 0x13e4a0 [C8 (Z_to_bv 64 4096)] ->
  rw_cells asegs m 0x1404c8 [C8 (Z_to_bv 64 0)] ->
  (* [comment removed for export] *)
  rw_cells asegs m 0x13e488 [C1 (Z_to_bv 8 (if ia then 1 else 0)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  stk asegs m 0xafc00 (0xafc00 + 0x81030) ->
  (ia = true -> forall j, 0 <= j < 32768 -> bytes_at asegs m (0xafc08 + 8 * j) (le8 (Z_to_bv 64 0))) ->
  (* [comment removed for export] *)
  rw_cells asegs m (ctx + 8) [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m t [C8 (Z_to_bv 64 ctx); C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)] ->
  rw_cells asegs m (t + 40) [C1 (Z_to_bv 8 0)] -> rw_cells asegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  0 < ctx -> AIMG_HI <= ctx -> ctx + 4096 <= ATOP ->
  iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  (* [comment removed for export] *)
  rw_cells asegs m hm [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  rw_cells asegs m (hm + 16) [C8 uw] -> 0 <= b1 < 256 -> Z.land b1 3 = 1 -> 0 <= n < 2^32 -> hm mod 16 = 0 ->
  ablk hm (hm + 16 + rup n 8) -> tclr hm 24 -> hm + 24 <= ATOP ->      (* [comment removed for export] *)
  (hm + 24 <= t \/ t + 4096 <= hm) -> (hm + 24 <= ctx \/ ctx + 4096 <= hm) ->
  (* [comment removed for export] *)
  ADEPOT DI L m ->
  AIMG_HI <= al_nodes L -> al_nodes L + 1048576 <= ATOP -> AIMG_HI <= al_store L -> al_store L + 8388608 <= ATOP ->
  (hm + 24 <= al_nodes L \/ al_nodes L + 1048576 <= hm) -> (hm + 24 <= al_store L \/ al_store L + 8388608 <= hm) ->
  (t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) -> (t + 4096 <= al_store L \/ al_store L + 8388608 <= t) ->
  (ctx + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= ctx) -> (ctx + 4096 <= al_store L \/ al_store L + 8388608 <= ctx) -> tclr (al_nodes L) 1048576 -> tclr (al_store L) 8388608 ->
  (* [comment removed for export] *)
  afree_unw RNG lo m top sp s0 ra trt ->
  bv_unsigned s0 <> bv_unsigned sp + 8 ->
  In (AFREE_PC :: trt) (al_U L) ->
  0 <= bot -> bot < bv_unsigned sp -> bot < top -> 4096 <= top <= 2^47 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 -> rng RNG hm 24 ->
  evtF asegs RNG (free_front_post L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n b1 actx lo trt m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 0).
Variable ia : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 1).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 2).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 3).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 4).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 5).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 6).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 7).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 8).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 9).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 10).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 11).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 12).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 13).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 14).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 15).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 16).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 17).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 18).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 19).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 20).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 21).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 22).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 23).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 24).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 25).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 26).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 27).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 28).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 29).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 30).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 31).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 32).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 33).
Variable F : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 34).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 35).
Variable m : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 36).
Variable t : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 37).
Variable ctx : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 38).
Variable hm : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 39).
Variable n : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 40).
Variable b1 : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 41).
Variable actx : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 42).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 43).
Variable top : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 44).
Variable bot : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 45).
Variable uw : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 46).
Variable sj : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 47).
Variable trt : ltac2:(SecDietF.SzSecF.ty 'free_front_spec__stmt 48).
#[using="Type"] Lemma free_front_spec__body : ltac:(let T := type of (fun (h : free_front_spec__stmt) => h L ia RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m t ctx hm n b1 actx lo top bot uw sj trt) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (ia, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (t, (ctx, (hm, (n, (b1, (actx, (lo, (top, (bot, (uw, (sj, trt))))))))))))))))))))))))))))))))))))))))))))))))) as _.

  intros ST CEIL LO MI TP Ha0 SP16 AC GOT6 MCS CF34 GPG PGC HK FL IAS IAM CT8 TT0 SW UW STATS LSJ CX0 C0 C1 T0 T1 CT2
         HD HUW B1 B13 NR AL HLO TCH HHI DHT DHC DEP N0 N1 R0 R1 DHN DHS DTN DTS DCN DCS XTNO XTST
         UNW S0NE TRU B0 BB BOTOP TOP RA4 RANE RIMG RTLS RSTK RCTX RT RNO RST RH. band_lin.   (* [comment removed for export] *)
  (pose proof (ablk_lin _ _ HLO) as ndP__; nd_pre ndP__ 4%nat; intros HL1 HL2 HL3 HL4; nd_post). unfold AIMG_HI in HL1. band_int HLO.   (* [comment removed for export] *)
  tclr_int TCH.      (* [comment removed for export] *)
  pose proof (afree_unw_length _ _ _ _ _ _ _ _ UNW) as LTRT.
  pose proof (afree_unw_sp47 _ _ _ _ _ _ _ _ UNW ltac:(clear -TOP; lia)) as SP47.
  pose proof AC as AC'. (nd_pre AC' 8%nat; intros INI RSS IMAX TI TK T88 TSD CT; nd_post).
  unfold AIMG_HI, AINSTANCE, ATP88, ATSD, ATSDI, ATSDK, AINITED, ARSSLIM, GOT_PGSZ, APGSZ, AFREE_SYM, AFREE_PC in *.
  word_range sp SPR. word_range s0 S0R. word_range ra RAR.
  box DHT. box DHC. box DHN. box DHS. box DTN. box DTS. box DCN. box DCS. box CT2.
  pose proof TT0 as TTx. rw_split TTx 1%nat TTc TT. clear TTc.
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (ficptA_spec (hm + 16) ia RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo);
      try eassumption; try (unfold AIA_FLAG, AIA_BASE, AIA_SIZE, AIA_MAP1; lia).
    all: try lazymatch goal with
         | |- rw_cells _ _ AIA_FLAG _ => exact FL
         | |- stk _ _ AIA_BASE _ => exact IAS
         | |- _ = true -> _ => exact IAM
         | |- rng _ _ _ => solve_rng
         end.
    all: match goal with |- ?G => idtac "REMA" G end. }
  cbv beta. intros ms1 PA. unfold ficptA_post in PA.
  (nd_pre PA 13%nat; intros t0a t1a t2a a6a a7a t3a t4a t5a t6a m1 junk1 junk2 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 10%nat; intros MUa WMa MIa STa FRA FRt FRs FL1 IAS1 IAM1; nd_post).
  (* [comment removed for export] *)
  pose proof FRs as FRs0. rw_split FRs0 7%nat FRsx FRsr. clear FRsx.
  destruct FRsr as [[_ BSR] _]. cbn [cells_bytes cbytes app] in BSR. rewrite app_nil_r in BSR.
  apply bytes_at_app in BSR. destruct BSR as [BS0 BRA]. rewrite length_le8 in BRA.
  replace (bv_unsigned sp + -16 + Z.of_nat 8) with (bv_unsigned sp - 8) in BRA by lia.
  replace (bv_unsigned sp + -16) with (bv_unsigned sp - 16) in BS0 by lia.
  assert (UC1 : forall tr, trt = bv_unsigned ra :: tr -> uchain m top 353060 (bv_unsigned sp) (bv_unsigned s0) 28%nat tr -> bv_unsigned sp + 16 < top ->
                uchain m1 top 353060 bot (bv_unsigned sp) 29%nat ([bv_unsigned ra] ++ tr)).
  { intros tr _ UC BTX. replace ([bv_unsigned ra] ++ tr) with ((if bv_unsigned ra =? 353060 then [] else [bv_unsigned ra]) ++ tr)
      by (replace (bv_unsigned ra =? 353060) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
    eapply (uc_step m1 top 353060 bot (bv_unsigned sp) 29%nat (bv_unsigned s0) (bv_unsigned ra) tr); try lia.
    - rewrite Z_to_bv_bv_unsigned. exact BS0.
    - rewrite Z_to_bv_bv_unsigned. exact BRA.
    - replace (bv_unsigned ra =? 353060) with false by (symmetry; apply Z.eqb_neq; lia). cbn [Nat.pred].
      destruct (Z_le_gt_dec (bv_unsigned sp + 16) (bv_unsigned s0)) as [GE|LT].
      + eapply uchain_frame; [exact UC|]. intros a Ha. apply MUa. cbn [outside]. rewrite unsigned_lit by lia. lia.
      + inversion UC; subst; [apply uc_stop; assumption | exfalso | exfalso]; Z.div_mod_to_equations; lia. }
  clear BS0 BRA.
  (* [comment removed for export] *)
  xport TI MUa WMa ltac:(lia). xport TK MUa WMa ltac:(lia). xport T88 MUa WMa ltac:(lia). xport TSD MUa WMa ltac:(lia).
  xport CT MUa WMa ltac:(lia). xport GPG MUa WMa ltac:(lia). xport PGC MUa WMa ltac:(lia). xport TT MUa WMa ltac:(lia).
  xport TT0 MUa WMa ltac:(lia). xport CT8 MUa WMa ltac:(lia).
  xport SW MUa WMa ltac:(lia). xport UW MUa WMa ltac:(lia). xport INI MUa WMa ltac:(lia).
  xport HD MUa WMa ltac:(lia). xport HUW MUa WMa ltac:(lia). xport HK MUa WMa ltac:(lia). xport STATS MUa WMa ltac:(rewrite LSJ; lia).
  assert (DEP1 : ADEPOT DI L m1).
  { eapply (adi_frame DI); [exact DEP | exact MUa | exact WMa |].
    repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq; lia|]). apply Forall_nil. }
  clear DEP.
  pose proof FRA as FRA0. rw_split FRA0 1%nat FRp FRz. rw_split FRz 1%nat SZC TAG.
  change 2040%nat with (8 * 255)%nat in FRt. destruct (u64arr_of_CB _ _ 255%nat _ FRt) as [TB LTB].
  pose proof FRs as FRs1. rw_split FRs1 1%nat BPJ REST.
  replace (bv_unsigned sp + -2120) with (bv_unsigned sp + -2128 + 8) in SZC by lia.
  replace (bv_unsigned sp + -2112) with (bv_unsigned sp + -2128 + 16) in TB by lia.
  replace (bv_unsigned sp + -72) with (bv_unsigned sp + -2128 + 2056) in BPJ by lia.
  (* [comment removed for export] *)
  step.                                                          (* [comment removed for export] *)
  name_sp sp (-2128).
  eapply evtF_cut with (P := unwind_impl_post (bv_unsigned sp + -2128) 353060 (bv_unsigned sp) t _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc lo trt m1).
  { destruct UNW as [(tr & Etr & UC & LTR & BTX & RTOP)|(Etr & TOPLE & SPLT)]; rewrite Etr.
    - eapply (unwind_impl_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (bv_unsigned sp + -2128) 353060 (bv_unsigned sp) ctx t top bot lo (words_of_bytes junk1) ([bv_unsigned ra] ++ tr)).
      all: try lazymatch goal with
         | |- stk _ _ _ _ => rewrite Hsp; exact STa
         | |- mem_inv _ _ => exact MIa
         | |- @eq word _ _ => rewrite ?Esp; first [reflexivity | exact TP | rewrite Z_to_bv_bv_unsigned; reflexivity | apply Z_to_bv_eqm; rewrite ?unsigned_lit by lia; lia]
         | |- ex _ => first [eexists; exact SZC | eexists; exact BPJ]
         | |- u64arr _ _ _ _ => exact TB
         | |- uchain _ _ _ _ _ _ _ => exact (UC1 tr Etr UC BTX)
         | |- _ \/ _ => unboxed CT2
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ (_ + 152) _ => exact CT
         | |- rw_cells _ _ (_ + 8) [C8 _; C8 _] => exact TT
         | |- rw_cells _ _ (_ + 40) _ => exact SW
         | |- rw_cells _ _ (_ + 3168) _ => exact UW
         end.
      all: try eassumption. all: try (unfold AIMG_HI; lia). all: try (Z.div_mod_to_equations; lia).
      all: match goal with |- ?G => idtac "REMU" G end.
    - eapply (unwind_impl_spec0 RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (bv_unsigned sp + -2128) 353060 (bv_unsigned sp) ctx t top bot lo (words_of_bytes junk1)).
      all: try lazymatch goal with
         | |- stk _ _ _ _ => rewrite Hsp; exact STa
         | |- mem_inv _ _ => exact MIa
         | |- @eq word _ _ => rewrite ?Esp; first [reflexivity | exact TP | rewrite Z_to_bv_bv_unsigned; reflexivity | apply Z_to_bv_eqm; rewrite ?unsigned_lit by lia; lia]
         | |- ex _ => first [eexists; exact SZC | eexists; exact BPJ]
         | |- u64arr _ _ _ _ => exact TB
         | |- _ \/ _ => unboxed CT2
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ (_ + 152) _ => exact CT
         | |- rw_cells _ _ (_ + 8) [C8 _; C8 _] => exact TT
         | |- rw_cells _ _ (_ + 40) _ => exact SW
         | |- rw_cells _ _ (_ + 3168) _ => exact UW
         end.
      all: try eassumption. all: try (unfold AIMG_HI; lia). all: try (Z.div_mod_to_equations; lia).
      all: match goal with |- ?G => idtac "REMU0" G end. }
  cbv beta. intros ms2 PU. unfold unwind_impl_post in PU.
  (nd_pre PU 18%nat; intros t0b t1b t2b a0b a1b a2b a3b a4b a5b a6b a7b t3b t4b t5b t6b m2 tb2 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 10%nat; intros MUu WMu MIu STu SZ2 TB2 LTB2 TRF2 BP2 UW2; nd_post).
  unname_sp. rewrite ?unsigned_lit in MUu by lia. rewrite ?unsigned_lit in STu by lia.
  replace (ret_pc (Z_to_bv 64 353152)) with (Z_to_bv 64 353152) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  (* [comment removed for export] *)
  assert (MU12 : munch [(bv_unsigned sp - 2288, bv_unsigned sp - 2128); (bv_unsigned sp - 2120, bv_unsigned sp - 2116); (bv_unsigned sp - 2112, bv_unsigned sp - 64); (t + 3168, t + 3169)]%Z m1 m2).
  { eapply munch_weaken; [| exact MUu]. unfold sub_fp; cbn [outside]; intros q Hq; lia. }
  xport TI MU12 WMu ltac:(lia). xport TK MU12 WMu ltac:(lia). xport T88 MU12 WMu ltac:(lia).
  xport TSD MU12 WMu ltac:(lia). xport CT MU12 WMu ltac:(ub CT2; ylia). xport CT8 MU12 WMu ltac:(ub CT2; ylia). xport TT0 MU12 WMu ltac:(lia).
  xport FRp MU12 WMu ltac:(lia). xport TAG MU12 WMu ltac:(lia). xport REST MU12 WMu ltac:(lia).
  xport HD MU12 WMu ltac:(ub DHT; ylia). xport HUW MU12 WMu ltac:(ub DHT; ylia). xport HK MU12 WMu ltac:(lia).
  xport STATS MU12 WMu ltac:(rewrite LSJ; lia).
  xport FL1 MU12 WMu ltac:(lia). xport IAS1 MU12 WMu ltac:(lia).
  assert (IAM2 : forall j, 0 <= j < 32768 -> bytes_at asegs m2 (0xafc08 + 8 * j) (le8 (Z_to_bv 64 0))).
  { intros j Hj. eapply bytes_at_agree; [exact (IAM1 j Hj)|].
    intros i Hi. apply MU12. cbn [outside]. rewrite length_le8 in Hi. rewrite wa_unsigned by lia. lia. }
  clear IAM1.
  assert (DEP2 : ADEPOT DI L m2).
  { eapply (adi_frame DI); [exact DEP1 | exact MU12 | exact WMu |].
    repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq; ub DTN; ub DTS; ylia|]). apply Forall_nil. }
  clear DEP1.
  (* [comment removed for export] *)
  rw_join SZ2 TAG SZT. rw_join FRp SZT SS.
  replace (bv_unsigned sp + -2112) with (bv_unsigned sp + -2128 + 16) in SS by lia.
  rewrite Z_to_bv_bv_unsigned in BP2. rw_join BP2 REST FRS.
  replace (bv_unsigned sp + -2128 + 2056) with (bv_unsigned sp + -72) in FRS by lia.
  (* [comment removed for export] *)
  zstep. zstep. step. step.                                      (* [comment removed for export] *)
  step.                                                          (* [comment removed for export] *)
  name_sp sp (-2128).
  eapply evtF_cut.
  { eapply (dealloc_spec t hm (bv_unsigned sp + -2128) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 n b1 actx ctx lo uw sj).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => rewrite Hsp; exact STu
         | |- mem_inv _ _ => exact MIu
         | |- @eq word _ _ => rewrite ?Esp; first [reflexivity | exact TP | apply Z_to_bv_eqm; rewrite ?unsigned_lit by lia; lia]
         | |- u64arr _ _ _ _ => exact STATS
         | |- _ \/ _ => first [unboxed DHT | unboxed DHC | unboxed CT2]
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ (_ + 152) _ => exact CT
         | |- rw_cells _ _ (_ + 16) _ => exact HUW
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD
         | |- rw_cells _ _ AFHOOK _ => exact HK
         end.
    all: try eassumption. all: try (unfold AIMG_HI; lia).
    all: match goal with |- ?G => idtac "REMD" G end. }
  cbv beta. intros ms3 PD. unfold dealloc_post in PD.
  (nd_pre PD 14%nat; intros t0c t1c t2c a4c a5c a6c a7c t3c t4c t5c t6c m3 sj3 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 8%nat; intros MUd WMd MId STd HD3 FC3 STATS3 LSJ3; nd_post).
  unname_sp. rewrite ?unsigned_lit in MUd by lia. rewrite ?unsigned_lit in STd by lia.
  (* [comment removed for export] *)
  xport TI MUd WMd ltac:(lia). xport TK MUd WMd ltac:(lia). xport T88 MUd WMd ltac:(lia). xport TSD MUd WMd ltac:(lia).
  xport CT MUd WMd ltac:(ub DHC; ub CT2; ylia). xport CT8 MUd WMd ltac:(ub DHC; ub CT2; ylia). xport TT0 MUd WMd ltac:(ub DHT; ylia).
  xport SS MUd WMd ltac:(lia). xport TB2 MUd WMd ltac:(rewrite LTB2; lia). xport FRS MUd WMd ltac:(lia).
  xport UW2 MUd WMd ltac:(ub DHT; ylia). xport FL1 MUd WMd ltac:(lia). xport IAS1 MUd WMd ltac:(lia).
  assert (IAM3 : forall j, 0 <= j < 32768 -> bytes_at asegs m3 (0xafc08 + 8 * j) (le8 (Z_to_bv 64 0))).
  { intros j Hj. eapply bytes_at_agree; [exact (IAM2 j Hj)|].
    intros i Hi. apply MUd. cbn [outside]. rewrite length_le8 in Hi. rewrite wa_unsigned by lia. lia. }
  clear IAM2.
  assert (DEP3 : ADEPOT DI L m3).
  { eapply (adi_frame DI); [exact DEP2 | exact MUd | exact WMd |].
    repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq; ub DTN; ub DTS; ub DHN; ub DHS; ylia|]). apply Forall_nil. }
  clear DEP2.
  (* [comment removed for export] *)
  name_sp sp (-2128).
  eapply evtF_cut.
  { eapply (qchunk_spec DI L t hm (bv_unsigned sp + -2128) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m3 n ctx b1 actx lo
              (1 + Z.of_nat (length trt)) 353060 (Z_to_bv 64 18446744069414584320) (Z_to_bv 64 top) (Z_to_bv 64 bot) tb2 trt).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => rewrite Hsp; exact STd
         | |- mem_inv _ _ => exact MId
         | |- ADEPOT _ _ _ => exact DEP3
         | |- @eq word _ _ => rewrite ?Esp; first [reflexivity | exact TP | apply Z_to_bv_eqm; rewrite ?unsigned_lit by lia; lia]
         | |- u64arr _ _ _ _ => exact TB2
         | |- In _ _ => exact TRU
         | |- map _ _ = _ => exact TRF2
         | |- _ \/ _ => first [unboxed DHN | unboxed DHS | unboxed DHT | unboxed DHC | unboxed DTN | unboxed DTS | unboxed DCN | unboxed DCS | unboxed CT2]
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ (_ + 152) _ => exact CT
         | |- rw_cells _ _ (_ + 8) _ => exact CT8
         | |- rw_cells _ _ (_ + 16) _ => exact FC3
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD3
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _] => exact TT0
         | |- rw_cells _ _ (_ + -2128) _ => exact SS
         end.
    all: try eassumption. all: try (unfold AIMG_HI; cbn [length]; lia).
    all: match goal with |- ?G => idtac "REMQ" G end. }
  cbv beta. intros ms4 PQ. unfold qchunk_post in PQ.
  (nd_pre PQ 12%nat; intros id t0d t1d t2d a6d a7d t3d t4d t5d t6d m4 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 7%nat; intros MUq WMq MIq STq FC4 IDR DEP4; nd_post).
  unname_sp. rewrite ?unsigned_lit in MUq by lia. rewrite ?unsigned_lit in STq by lia.
  (* [comment removed for export] *)
  xport HD3 MUq WMq ltac:(ub DHN; ub DHS; ylia). xport STATS3 MUq WMq ltac:(rewrite LSJ3; ub DHT; ub DTN; ub DTS; ylia).
  xport UW2 MUq WMq ltac:(ub DHT; ub DTN; ub DTS; ylia). xport FL1 MUq WMq ltac:(lia). xport IAS1 MUq WMq ltac:(lia).
  xport SS MUq WMq ltac:(lia). xport TB2 MUq WMq ltac:(rewrite LTB2; lia). xport FRS MUq WMq ltac:(lia).
  assert (IAM4 : forall j, 0 <= j < 32768 -> bytes_at asegs m4 (0xafc08 + 8 * j) (le8 (Z_to_bv 64 0))).
  { intros j Hj. eapply bytes_at_agree; [exact (IAM3 j Hj)|].
    intros i Hi. apply MUq. cbn [outside]. rewrite length_le8 in Hi. rewrite wa_unsigned by lia. lia. }
  clear IAM3.
  assert (MU : munch (front_W L sp t hm) m m4).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUq]].
    eapply munch_trans; [| eapply munch_weaken; [| exact MUd]].
    eapply munch_trans; [| eapply munch_weaken; [| exact MUu]].
    eapply munch_weaken; [| exact MUa].
    all: unfold sub_fp; cbn [outside]; intros q Hq; lia. }
  assert (WM : wmono asegs m m4).
  { eapply wmono_trans; [exact WMa|]. eapply wmono_trans; [exact WMu|]. eapply wmono_trans; [exact WMd| exact WMq]. }
  apply evtF_done. unfold free_front_post.
  exists id. do 9 eexists. exists m4, sj3, tb2, junk2.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MIq|]. split; [exact STq|]. split; [exact IDR|].
  split; [exact HD3|]. split; [exact FC4|]. split; [exact STATS3|]. split; [exact LSJ3|]. split; [exact UW2|].
  split; [exact FL1|]. split; [exact IAS1|]. split; [exact IAM4|].
  split; [exact SS|]. split; [exact TB2|]. split; [exact LTB2|].
  split; [exact FRS|]. exact DEP4.
  Unshelve. all: try exact STa; try exact STu; try exact STd.
Qed.
End Zd1.
#[using="Type"] Lemma free_front_spec : ltac:(let t := eval cbv delta [free_front_spec__stmt] in free_front_spec__stmt in exact t).
Proof. exact free_front_spec__body. Qed.
End WithDepot.
End CANSEC1.
End TwB.
End F_afree_front.

(* [comment removed for export] *)
Module F_adeallocfn_front.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecSlog__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3 F_aunwind. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc1b__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_s__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_adrain__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aunwind OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc1b__A3W.F_aunwind2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_afree_s OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_aintal OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_afree_iseg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc__A3W.F_adealloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_aqchunk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_front OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc__A3W.F_adeallocfn.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.
(* [comment removed for export] *)
Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6303744 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} {tlsI : ABase.atlsT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6303744 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (sclr_int a n H G1 G2) 4%nat; intros k A B C; nd_post); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (iclr_int a n H G2) 5%nat; intros k A B C D; nd_post); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>      (* [comment removed for export] *)
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (iclr_int a n H G2) 5%nat; intros k A B C D; nd_post); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.


Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.


Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section WithDepot.
Variable DI : ADepotIface.

Notation front_W L sp t hm :=
  ([(bv_unsigned sp - 4096, bv_unsigned sp); (0xaf800, 0xaf800 + 0x81030); (0x13e088, 0x13e088 + 4);
    (t + 3168, t + 3169); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z) (only parsing).

Definition dfn_front_post (L : alayout) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t hm n b1 actx lo S : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (id : Z) (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) m' (sj' : list word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
                  (Z_to_bv 64 0xab270) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 (t + 208)) (Z_to_bv 64 S)
                  (Z_to_bv 64 hm) (Z_to_bv 64 n) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x37ff4) fc None m' (seg_rom asegs)
    /\ munch (front_W L sp t hm) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ 0 < id < 2^31
    /\ rw_cells asegs m' hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)]
    /\ rw_cells asegs m' (hm + 16) [C8 (Z_to_bv 64 id)]
    /\ u64arr asegs m' (t + 2800) sj' /\ length sj' = 46%nat
    /\ rw_cells asegs m' (t + 3168) [C1 (Z_to_bv 8 0)]
    /\ rw_cells asegs m' 0x13e088 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ stk asegs m' 0xaf800 (0xaf800 + 0x81030)
    /\ (forall j, 0 <= j < 32768 -> bytes_at asegs m' (0xaf808 + 8 * j) (le8 (Z_to_bv 64 0)))
    /\ ADEPOT DI L m'.

#[using="Type"] Lemma dfn_front_spec : forall (L : alayout) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem)
    (t ctx hm n b1 actx lo S sz pc : Z) (uw top bot : word) (sj tb : list word) (trt : list Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 1968 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 (hm + 16) -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 0 -> a4 = Z_to_bv 64 S -> a5 = Z_to_bv 64 1 ->
  (* [comment removed for export] *)
  allocA_cells m ctx t ->
  rw_cells asegs m 0x1400c8 [C8 (Z_to_bv 64 0)] ->
  (* [comment removed for export] *)
  rw_cells asegs m 0x13e088 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  stk asegs m 0xaf800 (0xaf800 + 0x81030) ->
  (forall j, 0 <= j < 32768 -> bytes_at asegs m (0xaf808 + 8 * j) (le8 (Z_to_bv 64 0))) ->
  (* [comment removed for export] *)
  rw_cells asegs m (ctx + 8) [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m t [C8 (Z_to_bv 64 ctx); C8 top; C8 bot] ->
  rw_cells asegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  0 < ctx -> AIMG_HI <= ctx -> ctx + 4096 <= ATOP ->
  iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  (* [comment removed for export] *)
  rw_cells asegs m hm [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  rw_cells asegs m (hm + 16) [C8 uw] -> 0 <= b1 < 256 -> Z.land b1 3 = 1 -> 0 <= n < 2^32 -> hm mod 16 = 0 ->
  ablk hm (hm + 16 + rup n 8) -> tclr hm 24 -> hm + 24 <= ATOP ->
  (hm + 24 <= t \/ t + 4096 <= hm) -> (hm + 24 <= ctx \/ ctx + 4096 <= hm) ->
  (* [comment removed for export] *)
  rw_cells asegs m S [C8 (Z_to_bv 64 (S + 16)); C4 (Z_to_bv 64 sz); C4 (Z_to_bv 64 0)] ->
  u64arr asegs m (S + 16) tb -> length tb = 255%nat ->
  sz = 1 + Z.of_nat (length trt) -> sz <= 255 ->
  map bv_unsigned (firstn (Datatypes.S (length trt)) tb) = pc :: trt -> In (pc :: trt) (al_U L) ->
  bv_unsigned sp <= S -> S + 2056 <= 2^47 ->
  (* [comment removed for export] *)
  ADEPOT DI L m ->
  AIMG_HI <= al_nodes L -> al_nodes L + 1048576 <= ATOP -> AIMG_HI <= al_store L -> al_store L + 8388608 <= ATOP ->
  (hm + 24 <= al_nodes L \/ al_nodes L + 1048576 <= hm) -> (hm + 24 <= al_store L \/ al_store L + 8388608 <= hm) ->
  (t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) -> (t + 4096 <= al_store L \/ al_store L + 8388608 <= t) ->
  (ctx + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= ctx) -> (ctx + 4096 <= al_store L \/ al_store L + 8388608 <= ctx) -> tclr (al_nodes L) 1048576 -> tclr (al_store L) 8388608 ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG S 2056 -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 -> rng RNG hm 24 ->
  evtF asegs RNG (dfn_front_post L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n b1 actx lo S m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x338f4) fc None m (seg_rom asegs)).
Proof.
  intros until trt.
  intros ST CEIL LO MI TP Ha0 Ha1 Ha2 Ha3 Ha4 Ha5 AC HK FL1 IAS1 IAM1 CT8 TT0 UW2 STATS LSJ CX0 C0 C1 T0 T1 CT2
         HD HUW B1 B13 NR AL HLO TCH HHI DHT DHC SS TB2 LTB2 SZE SZB TRF2 TRU SGE S47 DEP N0 N1 R0 R1 DHN DHS DTN DTS DCN DCS XTNO XTST
         RIMG RTLS RSTK RS RCTX RT RNO RST RH. band_lin.
  (pose proof (ablk_lin _ _ HLO) as ndP__; nd_pre ndP__ 4%nat; intros HL1 HL2 HL3 HL4; nd_post). unfold AIMG_HI in HL1. band_int HLO.
  tclr_int TCH.
  pose proof AC as AC'. (nd_pre AC' 8%nat; intros INI RSS IMAX TI TK T88 TSD CT; nd_post).
  unfold AIMG_HI, AINSTANCE, ATP88, ATSD, ATSDI, ATSDK, AINITED, ARSSLIM in *.
  word_range sp SPR.
  box DHT. box DHC. box DHN. box DHS. box DTN. box DTS. box DCN. box DCS. box CT2.
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (dealloc_fn_spec t hm S RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n b1 actx ctx lo uw sj).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact ST
         | |- mem_inv _ _ => exact MI
         | |- @eq word _ _ => first [exact TP | exact Ha0 | exact Ha1 | exact Ha2 | exact Ha3 | exact Ha4 | exact Ha5]
         | |- u64arr _ _ _ _ => exact STATS
         | |- _ \/ _ => first [unboxed DHT | unboxed DHC | unboxed CT2]
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ (_ + 152) _ => exact CT
         | |- rw_cells _ _ (_ + 16) _ => exact HUW
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD
         | |- rw_cells _ _ AFHOOK _ => exact HK
         end.
    all: try eassumption. all: try (unfold AIMG_HI; lia).
    all: match goal with |- ?G => idtac "REMD" G end. }
  cbv beta. intros ms3 PD. unfold dealloc_post in PD.
  (nd_pre PD 14%nat; intros t0c t1c t2c a4c a5c a6c a7c t3c t4c t5c t6c m3 sj3 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 8%nat; intros MUd WMd MId STd HD3 FC3 STATS3 LSJ3; nd_post).
  (* [comment removed for export] *)
  xport TI MUd WMd ltac:(lia). xport TK MUd WMd ltac:(lia). xport T88 MUd WMd ltac:(lia). xport TSD MUd WMd ltac:(lia).
  xport CT MUd WMd ltac:(ub DHC; ub CT2; lia). xport CT8 MUd WMd ltac:(ub DHC; ub CT2; lia). xport TT0 MUd WMd ltac:(ub DHT; lia).
  xport SS MUd WMd ltac:(lia). xport TB2 MUd WMd ltac:(rewrite LTB2; lia).
  xport UW2 MUd WMd ltac:(ub DHT; lia). xport FL1 MUd WMd ltac:(lia). xport IAS1 MUd WMd ltac:(lia).
  assert (IAM3 : forall j, 0 <= j < 32768 -> bytes_at asegs m3 (0xaf808 + 8 * j) (le8 (Z_to_bv 64 0))).
  { intros j Hj. eapply bytes_at_agree; [exact (IAM1 j Hj)|].
    intros i Hi. apply MUd. cbn [outside]. rewrite length_le8 in Hi. rewrite wa_unsigned by lia. lia. }
  clear IAM1.
  assert (DEP3 : ADEPOT DI L m3).
  { eapply (adi_frame DI); [exact DEP | exact MUd | exact WMd |].
    repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq; ub DTN; ub DTS; ub DHN; ub DHS; lia|]). apply Forall_nil. }
  clear DEP.
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (qchunk_spec DI L t hm S RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m3 n ctx b1 actx lo
              sz pc (Z_to_bv 64 18446744069414584320) top bot tb trt).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact STd
         | |- mem_inv _ _ => exact MId
         | |- ADEPOT _ _ _ => exact DEP3
         | |- @eq word _ _ => first [reflexivity | exact TP]
         | |- u64arr _ _ _ _ => exact TB2
         | |- In _ _ => exact TRU
         | |- map _ _ = _ => exact TRF2
         | |- _ \/ _ => first [unboxed DHN | unboxed DHS | unboxed DHT | unboxed DHC | unboxed DTN | unboxed DTS | unboxed DCN | unboxed DCS | unboxed CT2]
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ (_ + 152) _ => exact CT
         | |- rw_cells _ _ (_ + 8) _ => exact CT8
         | |- rw_cells _ _ (_ + 16) _ => exact FC3
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD3
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _] => exact TT0
         | |- rw_cells _ _ _ [C8 _; C4 _; C4 _] => exact SS
         end.
    all: try eassumption. all: try (unfold AIMG_HI; cbn [length]; lia).
    all: match goal with |- ?G => idtac "REMQ" G end. }
  cbv beta. intros ms4 PQ. unfold qchunk_post in PQ.
  (nd_pre PQ 12%nat; intros id t0d t1d t2d a6d a7d t3d t4d t5d t6d m4 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 7%nat; intros MUq WMq MIq STq FC4 IDR DEP4; nd_post).
  (* [comment removed for export] *)
  xport HD3 MUq WMq ltac:(ub DHN; ub DHS; lia). xport STATS3 MUq WMq ltac:(rewrite LSJ3; ub DHT; ub DTN; ub DTS; lia).
  xport UW2 MUq WMq ltac:(ub DHT; ub DTN; ub DTS; lia). xport FL1 MUq WMq ltac:(lia). xport IAS1 MUq WMq ltac:(lia).
  assert (IAM4 : forall j, 0 <= j < 32768 -> bytes_at asegs m4 (0xaf808 + 8 * j) (le8 (Z_to_bv 64 0))).
  { intros j Hj. eapply bytes_at_agree; [exact (IAM3 j Hj)|].
    intros i Hi. apply MUq. cbn [outside]. rewrite length_le8 in Hi. rewrite wa_unsigned by lia. lia. }
  clear IAM3.
  assert (MU : munch (front_W L sp t hm) m m4).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUq]].
    eapply munch_weaken; [| exact MUd].
    all: unfold sub_fp; cbn [outside]; intros q Hq; lia. }
  assert (WM : wmono asegs m m4) by (eapply wmono_trans; [exact WMd| exact WMq]).
  apply evtF_done. unfold dfn_front_post.
  exists id. do 9 eexists. exists m4, sj3.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MIq|]. split; [exact STq|]. split; [exact IDR|].
  split; [exact HD3|]. split; [exact FC4|]. split; [exact STATS3|]. split; [exact LSJ3|]. split; [exact UW2|].
  split; [exact FL1|]. split; [exact IAS1|]. split; [exact IAM4|]. exact DEP4.
  Unshelve. all: try exact ST; try exact STd.
Qed.
End WithDepot.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aunwind.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc1b__A3W.F_aunwind2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_afree_s.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_aintal.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_afree_iseg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc__A3W.F_adealloc.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_aqchunk.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_front.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc__A3W.F_adeallocfn.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.
(* [comment removed for export] *)
Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6307840 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6307840 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (sclr_int a n H G1 G2) 4%nat; intros k A B C; nd_post); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (iclr_int a n H G2) 5%nat; intros k A B C D; nd_post); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>      (* [comment removed for export] *)
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (iclr_int a n H G2) 5%nat; intros k A B C D; nd_post); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.


Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.


Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section WithDepot.
Variable DI : ADepotIface.

Notation front_W L sp t hm :=
  ([(bv_unsigned sp - 4096, bv_unsigned sp); (0xafc00, 0xafc00 + 0x81030); (0x13e488, 0x13e488 + 4);
    (t + 3168, t + 3169); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z) (only parsing).

Definition dfn_front_post (L : alayout) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t hm n b1 actx lo S : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (id : Z) (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) m' (sj' : list word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
                  (Z_to_bv 64 0xab670) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 (t + 208)) (Z_to_bv 64 S)
                  (Z_to_bv 64 hm) (Z_to_bv 64 n) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x3805c) fc None m' (seg_rom asegs)
    /\ munch (front_W L sp t hm) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ 0 < id < 2^31
    /\ rw_cells asegs m' hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)]
    /\ rw_cells asegs m' (hm + 16) [C8 (Z_to_bv 64 id)]
    /\ u64arr asegs m' (t + 2800) sj' /\ length sj' = 46%nat
    /\ rw_cells asegs m' (t + 3168) [C1 (Z_to_bv 8 0)]
    /\ rw_cells asegs m' 0x13e488 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ stk asegs m' 0xafc00 (0xafc00 + 0x81030)
    /\ (forall j, 0 <= j < 32768 -> bytes_at asegs m' (0xafc08 + 8 * j) (le8 (Z_to_bv 64 0)))
    /\ ADEPOT DI L m'.

#[using="Type"] Lemma dfn_front_spec : forall (L : alayout) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem)
    (t ctx hm n b1 actx lo S sz pc : Z) (uw top bot : word) (sj tb : list word) (trt : list Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 1968 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 (hm + 16) -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 0 -> a4 = Z_to_bv 64 S -> a5 = Z_to_bv 64 1 ->
  (* [comment removed for export] *)
  allocA_cells m ctx t ->
  rw_cells asegs m 0x1404c8 [C8 (Z_to_bv 64 0)] ->
  (* [comment removed for export] *)
  rw_cells asegs m 0x13e488 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  stk asegs m 0xafc00 (0xafc00 + 0x81030) ->
  (forall j, 0 <= j < 32768 -> bytes_at asegs m (0xafc08 + 8 * j) (le8 (Z_to_bv 64 0))) ->
  (* [comment removed for export] *)
  rw_cells asegs m (ctx + 8) [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m t [C8 (Z_to_bv 64 ctx); C8 top; C8 bot] ->
  rw_cells asegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  0 < ctx -> AIMG_HI <= ctx -> ctx + 4096 <= ATOP ->
  iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  (* [comment removed for export] *)
  rw_cells asegs m hm [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  rw_cells asegs m (hm + 16) [C8 uw] -> 0 <= b1 < 256 -> Z.land b1 3 = 1 -> 0 <= n < 2^32 -> hm mod 16 = 0 ->
  ablk hm (hm + 16 + rup n 8) -> tclr hm 24 -> hm + 24 <= ATOP ->
  (hm + 24 <= t \/ t + 4096 <= hm) -> (hm + 24 <= ctx \/ ctx + 4096 <= hm) ->
  (* [comment removed for export] *)
  rw_cells asegs m S [C8 (Z_to_bv 64 (S + 16)); C4 (Z_to_bv 64 sz); C4 (Z_to_bv 64 0)] ->
  u64arr asegs m (S + 16) tb -> length tb = 255%nat ->
  sz = 1 + Z.of_nat (length trt) -> sz <= 255 ->
  map bv_unsigned (firstn (Datatypes.S (length trt)) tb) = pc :: trt -> In (pc :: trt) (al_U L) ->
  bv_unsigned sp <= S -> S + 2056 <= 2^47 ->
  (* [comment removed for export] *)
  ADEPOT DI L m ->
  AIMG_HI <= al_nodes L -> al_nodes L + 1048576 <= ATOP -> AIMG_HI <= al_store L -> al_store L + 8388608 <= ATOP ->
  (hm + 24 <= al_nodes L \/ al_nodes L + 1048576 <= hm) -> (hm + 24 <= al_store L \/ al_store L + 8388608 <= hm) ->
  (t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) -> (t + 4096 <= al_store L \/ al_store L + 8388608 <= t) ->
  (ctx + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= ctx) -> (ctx + 4096 <= al_store L \/ al_store L + 8388608 <= ctx) -> tclr (al_nodes L) 1048576 -> tclr (al_store L) 8388608 ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG S 2056 -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 -> rng RNG hm 24 ->
  evtF asegs RNG (dfn_front_post L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n b1 actx lo S m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3395c) fc None m (seg_rom asegs)).
Proof.
  intros until trt.
  intros ST CEIL LO MI TP Ha0 Ha1 Ha2 Ha3 Ha4 Ha5 AC HK FL1 IAS1 IAM1 CT8 TT0 UW2 STATS LSJ CX0 C0 C1 T0 T1 CT2
         HD HUW B1 B13 NR AL HLO TCH HHI DHT DHC SS TB2 LTB2 SZE SZB TRF2 TRU SGE S47 DEP N0 N1 R0 R1 DHN DHS DTN DTS DCN DCS XTNO XTST
         RIMG RTLS RSTK RS RCTX RT RNO RST RH. band_lin.
  (pose proof (ablk_lin _ _ HLO) as ndP__; nd_pre ndP__ 4%nat; intros HL1 HL2 HL3 HL4; nd_post). unfold AIMG_HI in HL1. band_int HLO.
  tclr_int TCH.
  pose proof AC as AC'. (nd_pre AC' 8%nat; intros INI RSS IMAX TI TK T88 TSD CT; nd_post).
  unfold AIMG_HI, AINSTANCE, ATP88, ATSD, ATSDI, ATSDK, AINITED, ARSSLIM in *.
  word_range sp SPR.
  box DHT. box DHC. box DHN. box DHS. box DTN. box DTS. box DCN. box DCS. box CT2.
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (dealloc_fn_spec t hm S RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n b1 actx ctx lo uw sj).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact ST
         | |- mem_inv _ _ => exact MI
         | |- @eq word _ _ => first [exact TP | exact Ha0 | exact Ha1 | exact Ha2 | exact Ha3 | exact Ha4 | exact Ha5]
         | |- u64arr _ _ _ _ => exact STATS
         | |- _ \/ _ => first [unboxed DHT | unboxed DHC | unboxed CT2]
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ (_ + 152) _ => exact CT
         | |- rw_cells _ _ (_ + 16) _ => exact HUW
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD
         | |- rw_cells _ _ AFHOOK _ => exact HK
         end.
    all: try eassumption. all: try (unfold AIMG_HI; lia).
    all: match goal with |- ?G => idtac "REMD" G end. }
  cbv beta. intros ms3 PD. unfold dealloc_post in PD.
  (nd_pre PD 14%nat; intros t0c t1c t2c a4c a5c a6c a7c t3c t4c t5c t6c m3 sj3 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 8%nat; intros MUd WMd MId STd HD3 FC3 STATS3 LSJ3; nd_post).
  (* [comment removed for export] *)
  xport TI MUd WMd ltac:(lia). xport TK MUd WMd ltac:(lia). xport T88 MUd WMd ltac:(lia). xport TSD MUd WMd ltac:(lia).
  xport CT MUd WMd ltac:(ub DHC; ub CT2; lia). xport CT8 MUd WMd ltac:(ub DHC; ub CT2; lia). xport TT0 MUd WMd ltac:(ub DHT; lia).
  xport SS MUd WMd ltac:(lia). xport TB2 MUd WMd ltac:(rewrite LTB2; lia).
  xport UW2 MUd WMd ltac:(ub DHT; lia). xport FL1 MUd WMd ltac:(lia). xport IAS1 MUd WMd ltac:(lia).
  assert (IAM3 : forall j, 0 <= j < 32768 -> bytes_at asegs m3 (0xafc08 + 8 * j) (le8 (Z_to_bv 64 0))).
  { intros j Hj. eapply bytes_at_agree; [exact (IAM1 j Hj)|].
    intros i Hi. apply MUd. cbn [outside]. rewrite length_le8 in Hi. rewrite wa_unsigned by lia. lia. }
  clear IAM1.
  assert (DEP3 : ADEPOT DI L m3).
  { eapply (adi_frame DI); [exact DEP | exact MUd | exact WMd |].
    repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq; ub DTN; ub DTS; ub DHN; ub DHS; lia|]). apply Forall_nil. }
  clear DEP.
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (qchunk_spec DI L t hm S RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m3 n ctx b1 actx lo
              sz pc (Z_to_bv 64 18446744069414584320) top bot tb trt).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact STd
         | |- mem_inv _ _ => exact MId
         | |- ADEPOT _ _ _ => exact DEP3
         | |- @eq word _ _ => first [reflexivity | exact TP]
         | |- u64arr _ _ _ _ => exact TB2
         | |- In _ _ => exact TRU
         | |- map _ _ = _ => exact TRF2
         | |- _ \/ _ => first [unboxed DHN | unboxed DHS | unboxed DHT | unboxed DHC | unboxed DTN | unboxed DTS | unboxed DCN | unboxed DCS | unboxed CT2]
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ (_ + 152) _ => exact CT
         | |- rw_cells _ _ (_ + 8) _ => exact CT8
         | |- rw_cells _ _ (_ + 16) _ => exact FC3
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD3
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _] => exact TT0
         | |- rw_cells _ _ _ [C8 _; C4 _; C4 _] => exact SS
         end.
    all: try eassumption. all: try (unfold AIMG_HI; cbn [length]; lia).
    all: match goal with |- ?G => idtac "REMQ" G end. }
  cbv beta. intros ms4 PQ. unfold qchunk_post in PQ.
  (nd_pre PQ 12%nat; intros id t0d t1d t2d a6d a7d t3d t4d t5d t6d m4 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 7%nat; intros MUq WMq MIq STq FC4 IDR DEP4; nd_post).
  (* [comment removed for export] *)
  xport HD3 MUq WMq ltac:(ub DHN; ub DHS; lia). xport STATS3 MUq WMq ltac:(rewrite LSJ3; ub DHT; ub DTN; ub DTS; lia).
  xport UW2 MUq WMq ltac:(ub DHT; ub DTN; ub DTS; lia). xport FL1 MUq WMq ltac:(lia). xport IAS1 MUq WMq ltac:(lia).
  assert (IAM4 : forall j, 0 <= j < 32768 -> bytes_at asegs m4 (0xafc08 + 8 * j) (le8 (Z_to_bv 64 0))).
  { intros j Hj. eapply bytes_at_agree; [exact (IAM3 j Hj)|].
    intros i Hi. apply MUq. cbn [outside]. rewrite length_le8 in Hi. rewrite wa_unsigned by lia. lia. }
  clear IAM3.
  assert (MU : munch (front_W L sp t hm) m m4).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUq]].
    eapply munch_weaken; [| exact MUd].
    all: unfold sub_fp; cbn [outside]; intros q Hq; lia. }
  assert (WM : wmono asegs m m4) by (eapply wmono_trans; [exact WMd| exact WMq]).
  apply evtF_done. unfold dfn_front_post.
  exists id. do 9 eexists. exists m4, sj3.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MIq|]. split; [exact STq|]. split; [exact IDR|].
  split; [exact HD3|]. split; [exact FC4|]. split; [exact STATS3|]. split; [exact LSJ3|]. split; [exact UW2|].
  split; [exact FL1|]. split; [exact IAS1|]. split; [exact IAM4|]. exact DEP4.
  Unshelve. all: try exact ST; try exact STd.
Qed.
End WithDepot.
End CANSEC1.
End TwB.
End F_adeallocfn_front.

(* [comment removed for export] *)
Module F_afree_icpt.
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecSlog__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_adrain__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_tail. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_afree_iseg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_front OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tail.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
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
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.
(* [comment removed for export] *)
Local Ltac qlia := first [ LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                         | LiaTuning.zify_prune; Zify.zify; xlia zchecker ].
Local Ltac leaf2 := first [ left; qlia | right; qlia | qlia ].
Local Ltac band_leaf :=
  first [ leaf2
        | match goal with B : sclr ?a _ |- context [?a] =>
            let B' := fresh "BB" in pose proof B as B'; unfold sclr, KLS in B'; destruct B' as [B'|B']; leaf2 end
        | match goal with B : iclr ?a _ |- context [?a] =>
            let B' := fresh "BB" in pose proof B as B'; unfold iclr, AIMG_LO, AIMG_HI in B'; destruct B' as [_ [B'|B']]; leaf2 end
        | match goal with B : ablk ?a _ |- context [?a] =>
            let B' := fresh "BB" in pose proof B as B'; unfold ablk, KLS, AIMG_HI in B'; destruct B' as [[? B']|[B' ?]]; leaf2 end
        | lia ].
Local Ltac band_disj := cbn [disjoint_from fst snd]; repeat match goal with |- _ /\ _ => split end; first [exact I | band_leaf].
(* [comment removed for export] *)
Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6303744 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} {tlsI : ABase.atlsT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6303744 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (sclr_int a n H G1 G2) 4%nat; intros k A B C; nd_post); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (iclr_int a n H G2) 5%nat; intros k A B C D; nd_post); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>      (* [comment removed for export] *)
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (iclr_int a n H G2) 5%nat; intros k A B C D; nd_post); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.


Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
#[using="Type"] Lemma rw_cells_of_u64arr : forall m A ws,
  u64arr asegs m A ws -> rw_cells asegs m A [CB (8 * length ws) (u64s ws)].
Proof.
  intros m A ws [B W]. split; [split|].
  - cbn. split; [apply u64s_length| exact I].
  - cbn [cells_bytes cbytes app]. rewrite app_nil_r. exact B.
  - cbn [cells_size csize Nat.add]. replace (Z.of_nat (8 * length ws + 0)) with (8 * Z.of_nat (length ws)) by lia. exact W.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma poison_cells_frame2 : forall m m' W,
  poison_cells m -> munch W m m' -> wmono asegs m m' ->
  Forall (fun iv => 0x1401a8 <= fst iv \/ (0xaf2fc <= fst iv /\ snd iv <= 0x1401a0) \/ snd iv <= 0xa54a0) W -> poison_cells m'.   (* [comment removed for export] *)
Proof.
  intros m m' W PC MU WM HW.
  assert (D : forall A n, 0xa54a0 <= A -> (A + n <= 0xaf2fc \/ (0x1401a0 <= A /\ A + n <= 0x1401a8)) -> disjoint_from W A n).
  { intros A n HA HB. clear MU. induction HW as [|[lo hi] W H1 H2 IH]; cbn in *; [exact I|]. split; [lia| exact IH]. }
  unfold poison_cells in *.
  (nd_pre PC 7%nat; intros P1 P2 P3 P4 P5 P6 P7; nd_post).
  repeat split; (eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply D; cbn; lia]).
Qed.

(* [comment removed for export] *)
Definition ek_seps (ek : enq_kind) (L : alayout) (hm lst : Z) : Prop :=
  match ek with
  | EkAppend _ _ _ _ _ _ _ _ =>
         (hm + 24 <= lst \/ lst + 8192 <= hm)
      /\ (al_nodes L + 1048576 <= lst \/ lst + 8192 <= al_nodes L) /\ (al_store L + 8388608 <= lst \/ lst + 8192 <= al_store L)
  | EkNew full _ _ _ _ _ _ _ _ _ b _ =>
         (hm + 24 <= b \/ b + 8192 <= hm)
      /\ (al_nodes L + 1048576 <= b \/ b + 8192 <= al_nodes L) /\ (al_store L + 8388608 <= b \/ b + 8192 <= al_store L)
      /\ (full = true ->
             (hm + 24 <= lst \/ lst + 8192 <= hm)
          /\ (al_nodes L + 1048576 <= lst \/ lst + 8192 <= al_nodes L) /\ (al_store L + 8388608 <= lst \/ lst + 8192 <= al_store L))
  end.

Definition dk_seps (g : gqd) (L : alayout) (hm : Z) : Prop :=
  g_drain g = true -> g_full g = true ->
     (hm + 24 <= g_lst g \/ g_lst g + 8 <= hm)
  /\ (al_nodes L + 1048576 <= g_lst g \/ g_lst g + 8192 <= al_nodes L) /\ (al_store L + 8388608 <= g_lst g \/ g_lst g + 8192 <= al_store L).

(* [comment removed for export] *)
#[using="Type"] Lemma ek_pre_pure : forall ek RNG L t nb lst n hm m,
  ek_pre ek RNG t nb lst n hm m -> ek_seps ek L hm lst ->
  iclr t 4096 -> AIMG_HI <= hm -> AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L ->
     (hm + 24 <= lst \/ lst + 8192 <= hm) /\ (hm + 24 <= ek_b ek lst \/ ek_b ek lst + 8192 <= hm)
  /\ (t + 4096 <= lst \/ lst + 8192 <= t \/ lst = 0) /\ (t + 4096 <= ek_b ek lst \/ ek_b ek lst + 8192 <= t)
  /\ (al_nodes L + 1048576 <= lst \/ lst + 8192 <= al_nodes L) /\ (al_store L + 8388608 <= lst \/ lst + 8192 <= al_store L)
  /\ (al_nodes L + 1048576 <= ek_b ek lst \/ ek_b ek lst + 8192 <= al_nodes L) /\ (al_store L + 8388608 <= ek_b ek lst \/ ek_b ek lst + 8192 <= al_store L)
  /\ 0 <= lst /\ lst + 8192 <= ATOP /\ 0 <= ek_b ek lst /\ ek_b ek lst + 8192 <= ATOP
  /\ (lst = 0 \/ 0x10007fff8000 <= lst) /\ 0x10007fff8000 <= ek_b ek lst.
Proof.
  intros ek RNG L t nb lst n hm m EK ES T0 H0 N0 R0. unfold AIMG_HI in *. band_lin.   (* [comment removed for export] *)
  destruct ek as [nx bsz cnt hs cnt24' maxc' csz' stj' | full nx bsz cnt24 maxc csz stj idxw chunks spacebeg b hs0]; cbn [ek_pre ek_seps ek_b] in *.
  - (nd_pre EK 16%nat; intros NB1 LB CNT BSZ BSZN NX LA LEN LJ L0 L1 DTL DHL CR' STS' RL; nd_post). atop_facts. lia.
  - (nd_pre EK 20%nat; intros FULL SB CR CH LCH CNT NTH IXS STS HB BJ SBP B0 BL1 DTB DTL DBL DHB DHL RB; nd_post).
    (nd_pre ES 4%nat; intros S1 S2 S3 S4; nd_post). atop_facts.
    destruct full; [(nd_pre FULL 9%nat; intros NB1 LB NX BSZ L0 L1 LA0 LEN0 RL; nd_post); specialize (S4 eq_refl) | destruct FULL as [NB0 LST0]]; lia.
Qed.

#[using="Type"] Lemma dk_pre_pure : forall ek g RNG L t lst hm qb' m,
  dk_pre ek g RNG t lst hm qb' m -> dk_seps g L hm ->
  iclr t 4096 -> AIMG_HI <= hm -> AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L ->
  (hm + 24 <= lst \/ lst + 8192 <= hm) -> (t + 4096 <= lst \/ lst + 8192 <= t \/ lst = 0) ->
  (al_nodes L + 1048576 <= lst \/ lst + 8192 <= al_nodes L) -> (al_store L + 8388608 <= lst \/ lst + 8192 <= al_store L) ->
  0 <= lst -> lst + 8192 <= ATOP -> (lst = 0 \/ 0x10007fff8000 <= lst) ->
     (hm + 24 <= dk_glst g lst \/ dk_glst g lst + 8 <= hm) /\ (t + 4096 <= dk_glst g lst \/ dk_glst g lst + 8 <= t)
  /\ (al_nodes L + 1048576 <= dk_glst g lst \/ dk_glst g lst + 8 <= al_nodes L) /\ (al_store L + 8388608 <= dk_glst g lst \/ dk_glst g lst + 8 <= al_store L)
  /\ 0 <= dk_glst g lst /\ dk_glst g lst + 8 <= ATOP /\ (dk_glst g lst = 0 \/ 0x10007fff8000 <= dk_glst g lst).
Proof.
  intros ek g RNG L t lst hm qb' m DK DS T0 H0 N0 R0 P1 P3 P5 P6 LNN LHI LZH. unfold AIMG_HI in *. band_lin.   (* [comment removed for export] *)
  unfold dk_pre, dk_seps, dk_glst in *.
  (nd_pre DK 7%nat; intros MX GC GNB GQB GFST GLST DK'; nd_post).
  destruct (g_drain g); [| lia].
  (nd_pre DK' 3%nat; intros QB1 GQ GFULL; nd_post).
  destruct (g_full g); [(nd_pre GFULL 9%nat; intros G1 GLB G3 G4 G5 G6 G7 G8 G9; nd_post); specialize (DS eq_refl eq_refl) | destruct GFULL as [GNB0 GLST0]];
    atop_facts; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma outside_In : forall W x jv, outside W x -> In jv W -> ~ (fst jv <= x < snd jv).
Proof.
  induction W as [|[lo hi] W IH]; cbn; intros x jv Ho Hin; [tauto|].
  destruct Ho as [H1 H2]. destruct Hin as [<-|Hin]; [exact H1| exact (IH _ _ H2 Hin)].
Qed.
#[using="Type"] Lemma sub_fp_by_incl : forall W W',
  Forall (fun iv => Exists (fun jv => fst jv <= fst iv /\ snd iv <= snd jv) W') W -> sub_fp W W'.
Proof.
  intros W W' HF x Ho. induction HF as [|[lo hi] W HE HF IH]; cbn; [exact I|].
  split; [| exact IH]. apply Exists_exists in HE. (nd_pre HE 4%nat; intros jv Hin H1 H2; nd_post). cbn in H1, H2.
  pose proof (outside_In W' x jv Ho Hin). lia.
Qed.
(* [comment removed for export] *)
End CANSEC1.
Ltac find_iv s :=
  first [ apply Exists_cons_hd; cbn [fst snd]; split; apply Z.le_refl
        | apply Exists_cons_hd; cbn [fst snd]; solve [clear - s; lia]
        | apply Exists_cons_tl; find_iv s ].
Ltac solve_sub_fp s :=
  apply sub_fp_by_incl; repeat (apply Forall_cons; [find_iv s|]); apply Forall_nil.

(* [comment removed for export] *)
Ltac reasm :=
  repeat (lazymatch goal with
          | |- rng _ _ _ => assumption
          | |- ex _ => eexists; eassumption
          | |- _ /\ _ => first [assumption | split; [first [assumption | lia | eexists; eassumption] | ]]
          | |- _ => first [assumption | lia | exact I]
          end).

Section CANSEC2. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section Transport.
(* [comment removed for export] *)
Variables (L : alayout) (sp : word) (t hm lo : Z) (m m' : amem).
Hypothesis MU : munch [(bv_unsigned sp - 4096, bv_unsigned sp); (0xaf800, 0xaf800 + 0x81030); (0x13e088, 0x13e088 + 4);
    (t + 3168, t + 3169); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368);
    (0x1804c8, 0x5d0510); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z m m'.
Hypothesis WM : wmono asegs m m'.
Hypotheses (CEIL : ATOP <= lo) (LO : lo <= bv_unsigned sp - 4096) (T0 : iclr t 4096) (T1 : t + 4096 <= ATOP)     (* [comment removed for export] *)
           (H0 : AIMG_HI <= hm) (DHT : hm + 24 <= t \/ t + 4096 <= hm) (N0 : AIMG_HI <= al_nodes L) (R0 : AIMG_HI <= al_store L)
           (DTN : t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) (DTS : t + 4096 <= al_store L \/ al_store L + 8388608 <= t).

#[using="sp lo MU WM CEIL LO T0 T1 H0 DHT N0 R0 DTN DTS"] Lemma ek_pre_front : forall ek RNG nb lst n,
  ek_pre ek RNG t nb lst n hm m -> ek_seps ek L hm lst -> ek_pre ek RNG t nb lst n hm m'.
Proof.
  intros ek RNG nb lst n EK ES. unfold AIMG_HI in *. band_lin.   (* [comment removed for export] *)
  destruct ek as [nx bsz cnt hs cnt24' maxc' csz' stj' | full nx bsz cnt24 maxc csz stj idxw chunks spacebeg b hs0]; cbn [ek_pre ek_seps] in *.
  - (nd_pre EK 16%nat; intros NB1 LB CNT BSZ BSZN NX LA LEN [junkt LJ] L0 L1 DTL DHL CR' STS' RL; nd_post). atop_facts.
    (nd_pre ES 3%nat; intros S1 S2 S3; nd_post).
    xport LB MU WM ltac:(clear -CEIL LO T0 T1 H0 DHT N0 R0 DTN DTS L0 L1 DTL DHL S1 S2 S3; lia). xport LA MU WM ltac:(rewrite LEN; clear -CEIL LO T0 T1 H0 DHT N0 R0 DTN DTS L0 L1 DTL DHL CNT S1 S2 S3; lia). xport LJ MU WM ltac:(clear -CEIL LO T0 T1 H0 DHT N0 R0 DTN DTS L0 L1 DTL DHL CNT S1 S2 S3; lia).   (* [comment removed for export] *)
    xport CR' MU WM ltac:(clear -CEIL LO T0 T1 H0 DHT N0 R0 DTN DTS; lia). xport STS' MU WM ltac:(clear -CEIL LO T0 T1 H0 DHT N0 R0 DTN DTS; lia).
    reasm.
  - (nd_pre EK 20%nat; intros FULL SB CR CH LCH CNT NTH IXS STS HB [junkb BJ] SBP B0 BL1 DTB DTL DBL DHB DHL RB; nd_post).
    (nd_pre ES 4%nat; intros S1 S2 S3 S4; nd_post). atop_facts.
    xport SB MU WM ltac:(clear -CEIL LO T0 T1 H0 DHT N0 R0 DTN DTS; lia). xport CR MU WM ltac:(clear -CEIL LO T0 T1 H0 DHT N0 R0 DTN DTS; lia). xport CH MU WM ltac:(rewrite LCH; clear -CEIL LO T0 T1 H0 DHT N0 R0 DTN DTS; lia). xport STS MU WM ltac:(clear -CEIL LO T0 T1 H0 DHT N0 R0 DTN DTS; lia). xport BJ MU WM ltac:(clear -CEIL LO T0 T1 H0 DHT N0 R0 DTN DTS B0 BL1 DTB DHB S1 S2 S3; lia).
    split.
    + destruct full; [| exact FULL]. (nd_pre FULL 9%nat; intros NB1 LB NX BSZ L0 L1 LA0 LEN0 RL; nd_post). specialize (S4 eq_refl). (nd_pre S4 3%nat; intros S5 S6 S7; nd_post).
      xport LB MU WM ltac:(clear -CEIL LO T0 T1 H0 DHT N0 R0 DTN DTS L0 L1 DTL DHL S5 S6 S7; lia). xport LA0 MU WM ltac:(rewrite LEN0; clear -CEIL LO T0 T1 H0 DHT N0 R0 DTN DTS L0 L1 DTL DHL S5 S6 S7; lia). reasm.
    + reasm.
Qed.

#[using="sp lo MU WM CEIL LO T0 T1 H0 DHT N0 R0 DTN DTS"] Lemma dk_pre_front : forall ek g RNG lst qb',
  dk_pre ek g RNG t lst hm qb' m -> dk_seps g L hm -> dk_pre ek g RNG t lst hm qb' m'.
Proof.
  intros ek g RNG lst qb' DK DS. unfold AIMG_HI in *. band_lin.   (* [comment removed for export] *)
  unfold dk_pre, dk_seps in *.
  (nd_pre DK 7%nat; intros MX GC GNB GQB GFST GLST DK'; nd_post).
  xport MX MU WM ltac:(lia). xport GC MU WM ltac:(lia).
  do 6 (split; [assumption|]).
  destruct (g_drain g); [| exact DK'].
  (nd_pre DK' 3%nat; intros QB1 GQ GFULL; nd_post). split; [exact QB1|]. split; [exact GQ|].
  destruct (g_full g); [| exact GFULL].
  (nd_pre GFULL 9%nat; intros G1 GLB G3 G4 G5 G6 G7 G8 G9; nd_post). specialize (DS eq_refl eq_refl). (nd_pre DS 3%nat; intros D1 D2 D3; nd_post). atop_facts.
  xport GLB MU WM ltac:(lia). reasm.
Qed.
End Transport.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithDepot.
Variable DI : ADepotIface.

Notation free_W L sp t hm n lst ek g :=
  ([(bv_unsigned sp - 4096, bv_unsigned sp); (0xaf800, 0xaf800 + 0x81030); (0x13e088, 0x13e088 + 4);
    (t + 3168, t + 3169); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608);
    (shad (hm + 16), shad (hm + 16) + shlen (rup n 8)); (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792);
    (lst, lst + qsz lst); (ek_b ek lst, ek_b ek lst + 8192);
    (0xab308, 0xab308 + 4); (0xab310, 0xab310 + 32); (dk_glst g lst, dk_glst g lst + 8)]%Z) (only parsing).

Definition free_fast_post (L : alayout) (ek : enq_kind) (g : gqd)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t hm n nb fst0 lst qb b1 actx lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (id : Z) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m' (sj' : list word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (free_W L sp t hm n lst ek g) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ 0 < id < 2^31
    /\ rw_cells asegs m' hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)]
    /\ rw_cells asegs m' (hm + 16) [C8 (Z_to_bv 64 id)]
    /\ rw_cells asegs m' (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) (repeat (Z_to_bv 8 253) (Z.to_nat (shlen (rup n 8))))]
    /\ rw_cells asegs m' (t + 80) (tcache_post g (ek_nb ek nb) (ek_fst ek fst0) (ek_lst ek lst) (qb + ek_delta ek n))
    /\ ek_post ek t lst hm n m'
    /\ dk_post g (ek_nb ek nb) (ek_fst ek fst0) (ek_lst ek lst) (qb + ek_delta ek n) m'
    /\ u64arr asegs m' (t + 2800) sj' /\ length sj' = 46%nat
    /\ rw_cells asegs m' (t + 3168) [C1 (Z_to_bv 8 0)]
    /\ rw_cells asegs m' 0x13e088 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ stk asegs m' 0xaf800 (0xaf800 + 0x81030)
    /\ (forall j, 0 <= j < 32768 -> bytes_at asegs m' (0xaf808 + 8 * j) (le8 (Z_to_bv 64 0)))
    /\ ADEPOT DI L m'.

Definition free_fast_spec__stmt : Prop := forall (L : alayout) (ia : bool) (ek : enq_kind) (g : gqd) RNG
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem)
    (t ctx hm n b1 actx lo top bot nb fst0 lst qb : Z) (uw : word) (sj : list word) (sjunk : list byte) (trt : list Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 (hm + 16) ->
  bv_unsigned sp mod 16 = 0 ->
  (* [comment removed for export] *)
  allocA_cells m ctx t -> poison_cells m ->
  rw_cells asegs m 0xaf2fc [C4 (Z_to_bv 64 30)] ->
  rw_cells asegs m 0x14014a [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m 0xa5490 [C8 (Z_to_bv 64 0x13e0a0)] -> rw_cells asegs m 0x13e0a0 [C8 (Z_to_bv 64 4096)] ->
  rw_cells asegs m 0x1400c8 [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m 0xab2b0 [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->
  rw_cells asegs m 0xa54a8 [C8 (Z_to_bv 64 AFLAGS)] ->
  rw_cells asegs m 0xabe24 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->
  (* [comment removed for export] *)
  rw_cells asegs m 0x13e088 [C1 (Z_to_bv 8 (if ia then 1 else 0)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  stk asegs m 0xaf800 (0xaf800 + 0x81030) ->
  (ia = true -> forall j, 0 <= j < 32768 -> bytes_at asegs m (0xaf808 + 8 * j) (le8 (Z_to_bv 64 0))) ->
  (* [comment removed for export] *)
  rw_cells asegs m (ctx + 8) [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m t [C8 (Z_to_bv 64 ctx); C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)] ->
  rw_cells asegs m (t + 40) [C1 (Z_to_bv 8 0)] -> rw_cells asegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  rw_cells asegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= qb -> qb + n + 8192 < 2^62 -> 0 <= fst0 < 2^64 -> 0 <= lst < 2^64 ->
  0 < ctx -> sclr ctx 65536 -> ctx + 4096 <= ATOP ->
  sclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> t mod 4096 = 0 -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  (* [comment removed for export] *)
  rw_cells asegs m hm [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  rw_cells asegs m (hm + 16) [C8 uw] -> 0 <= b1 < 256 -> Z.land b1 3 = 1 -> 1 <= n <= Q_MAX -> hm mod 16 = 0 ->
  ablk hm (hm + 16 + rup n 8) -> tclr hm 24 -> hm + 16 + rup n 8 <= ATOP -> hm + 24 <= ATOP ->
  rw_cells asegs m (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) sjunk] ->
  (hm + 24 <= t \/ t + 4096 <= hm) -> (hm + 24 <= ctx \/ ctx + 4096 <= hm) ->
  (* [comment removed for export] *)
  ek_pre ek RNG t nb lst n hm m -> ek_seps ek L hm lst ->
  dk_pre ek g RNG t lst hm (qb + ek_delta ek n) m -> dk_seps g L hm ->
  (* [comment removed for export] *)
  ADEPOT DI L m ->
  sclr (al_nodes L) 1048576 -> al_nodes L + 1048576 <= ATOP -> sclr (al_store L) 8388608 -> al_store L + 8388608 <= ATOP ->
  (hm + 24 <= al_nodes L \/ al_nodes L + 1048576 <= hm) -> (hm + 24 <= al_store L \/ al_store L + 8388608 <= hm) ->
  (t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) -> (t + 4096 <= al_store L \/ al_store L + 8388608 <= t) ->
  (ctx + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= ctx) -> (ctx + 4096 <= al_store L \/ al_store L + 8388608 <= ctx) -> tclr (al_nodes L) 1048576 -> tclr (al_store L) 8388608 ->
  (* [comment removed for export] *)
  afree_unw RNG lo m top sp s0 ra trt ->
  bv_unsigned s0 <> bv_unsigned sp + 8 ->
  In (AFREE_PC :: trt) (al_U L) ->
  0 <= bot -> bot < bv_unsigned sp -> bot < top -> 4096 <= top <= 2^47 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 -> rng RNG hm 24 -> rng RNG (shad (hm + 16)) (shlen (rup n 8)) ->
  AIMG_HI <= ctx -> AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L -> iclr t 4096 ->      (* [comment removed for export] *)
  evtF asegs RNG (free_fast_post L ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n nb fst0 lst qb b1 actx lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 0).
Variable ia : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 1).
Variable ek : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 2).
Variable g : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 3).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 4).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 5).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 6).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 7).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 8).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 9).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 10).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 11).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 12).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 13).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 14).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 15).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 16).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 17).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 18).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 19).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 20).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 21).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 22).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 23).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 24).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 25).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 26).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 27).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 28).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 29).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 30).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 31).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 32).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 33).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 34).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 35).
Variable F : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 36).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 37).
Variable m : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 38).
Variable t : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 39).
Variable ctx : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 40).
Variable hm : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 41).
Variable n : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 42).
Variable b1 : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 43).
Variable actx : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 44).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 45).
Variable top : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 46).
Variable bot : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 47).
Variable nb : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 48).
Variable fst0 : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 49).
Variable lst : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 50).
Variable qb : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 51).
Variable uw : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 52).
Variable sj : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 53).
Variable sjunk : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 54).
Variable trt : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 55).
#[using="Type"] Lemma free_fast_spec__body : ltac:(let T := type of (fun (h : free_fast_spec__stmt) => h L ia ek g RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m t ctx hm n b1 actx lo top bot nb fst0 lst qb uw sj sjunk trt) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (ia, (ek, (g, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (t, (ctx, (hm, (n, (b1, (actx, (lo, (top, (bot, (nb, (fst0, (lst, (qb, (uw, (sj, (sjunk, trt)))))))))))))))))))))))))))))))))))))))))))))))))))))))) as _.

  intros ST CEIL LO MI TP Ha0 SP16 AC PC MCS CF34 GPG PGC HK QK GF FLG FL IAS IAM CT8 TT0 SW UW STATS LSJ QC NB QB QBN FST LST
         CX0 C0 C1 T0 T1 TAL CT2 HD HUW B1 B13 N AL HLO TCH HHI HCE SH DHT DHC EK ES DK DS DEP N0 N1 R0 R1 DHN DHS DTN DTS DCN DCS XTNO XTST
         UNW S0NE TRU B0 BB BOTOP TOP RA4 RANE RIMG RTLS RSTK RCTX RT RNO RST RH RSH CI NI SI TI.
  band_int TI. (pose proof (ablk_lin _ _ HLO) as ndP__; nd_pre ndP__ 4%nat; intros HL1 HL2 HL3 HL4; nd_post). unfold AIMG_HI in HL1. band_int HLO. band_lin. band_int C0. band_int T0. band_int N0. band_int R0.   (* [comment removed for export] *)
  pose proof (afree_unw_length _ _ _ _ _ _ _ _ UNW) as LTRT.
  pose proof (afree_unw_sp47 _ _ _ _ _ _ _ _ UNW ltac:(clear -TOP; lia)) as SP47.
  pose proof PC as PC'. destruct PC' as (GOT6 & _).
  assert (RUP : n <= rup n 8 <= n + 7 /\ rup n 8 mod 8 = 0) by (clear -N; unfold rup; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
  assert (SHB : 2148238848 <= shad (hm + 16) /\ shad (hm + 16) + shlen (rup n 8) <= 0x10007fff8000 /\ 0 < shlen (rup n 8)).
  { clear -N HLO HL1 HHI HCE. atop_facts. unfold shad, shlen, ASHOFF, rup in *. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold Q_MAX in *. Z.div_mod_to_equations. lia. }
  (pose proof (ek_pre_pure ek RNG L t nb lst n hm m EK ES TI ltac:(unfold AIMG_HI; lia) NI SI) as ndP__; nd_pre ndP__ 14%nat; intros PF1 PF2 PF3 PF4 PF5 PF6 PF7 PF8 PL0 PL1 PB0 PB1 PL2 PB2; nd_post).
  (pose proof (dk_pre_pure ek g RNG L t lst hm (qb + ek_delta ek n) m DK DS TI ltac:(unfold AIMG_HI; lia) NI SI PF1 PF3 PF5 PF6 PL0 PL1 PL2) as ndP__; nd_pre ndP__ 7%nat; intros DF1 DF2 DF3 DF4 DG0 DG1 DG2; nd_post).
  (pose proof (qsz_int lst PL0 ltac:(clear -PL1; atop_facts; lia)) as ndP__; nd_pre ndP__ 5%nat; intros zq QZ0 QZ1 QZ2 QZ3; nd_post).   (* [comment removed for export] *)
  unfold AIMG_HI, AFREE_SYM, AFREE_PC in *.
  word_range sp SPR.
  box DHT. box DHC. box DHN. box DHS. box DTN. box DTS. box DCN. box DCS. box CT2.
  box PF1. box PF2. box PF3. box PF4. box PF5. box PF6. box PF7. box PF8. box DF1. box DF2. box DF3. box DF4. box PL2. box DG2.
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (free_front_spec DI L ia RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
              t ctx hm n b1 actx lo top bot uw sj trt).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact ST | exact IAS]
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => exact AC
         | |- ADEPOT _ _ _ => exact DEP
         | |- afree_unw _ _ _ _ _ _ => exact UNW
         | |- In _ _ => exact TRU
         | |- u64arr _ _ _ _ => exact STATS
         | |- _ = true -> _ => exact IAM
         | |- _ \/ _ => first [unboxed DHT | unboxed DHC | unboxed DHN | unboxed DHS | unboxed DTN | unboxed DTS | unboxed DCN | unboxed DCS | unboxed CT2]
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _] => exact TT0
         | |- rw_cells _ _ (_ + 16) _ => exact HUW
         | |- rw_cells _ _ (_ + 8) _ => exact CT8
         | |- rw_cells _ _ (_ + 40) _ => exact SW
         | |- rw_cells _ _ (_ + 3168) _ => exact UW
         end.
    all: try eassumption. all: try (unfold AIMG_HI, Q_MAX in *; lia).
    all: match goal with |- ?G => idtac "REMF" G end. }
  cbv beta. intros ms1 PFR. unfold free_front_post in PFR.
  (nd_pre PFR 15%nat; intros id t0a t1a t2a a6a a7a t3a t4a t5a t6a m1 sj1 tb1 junk2 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 18%nat; intros MUf WMf MIf STf IDR HD1 FC1 STATS1 LSJ1 UW1 FL1 IAS1 IAM1 SS1 TB1 LTB1 FRS1 DEP1; nd_post).
  (* [comment removed for export] *)
  xport QK MUf WMf ltac:(lia). xport GF MUf WMf ltac:(lia). xport FLG MUf WMf ltac:(lia).
  xport QC MUf WMf ltac:(ub DHT; ub DTN; ub DTS; ylia).
  xport SH MUf WMf ltac:(band_disj).   (* [comment removed for export] *)
  assert (PC1 : poison_cells m1).
  { eapply poison_cells_frame2; [exact PC | exact MUf | exact WMf |].
    repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
  assert (EK1 : ek_pre ek RNG t nb lst n hm m1).
  { eapply (ek_pre_front L sp t hm lo m m1); [exact MUf | exact WMf | ..]; try (unfold AIMG_HI; lia).
    all: first [exact TI | unboxed DHT | unboxed DTN | unboxed DTS | exact EK | exact ES]. }
  assert (DK1 : dk_pre ek g RNG t lst hm (qb + ek_delta ek n) m1).
  { eapply (dk_pre_front L sp t hm lo m m1); [exact MUf | exact WMf | ..]; try (unfold AIMG_HI; lia).
    all: first [exact TI | unboxed DHT | unboxed DTN | unboxed DTS | exact DK | exact DS]. }
  clear EK DK PC.
  (* [comment removed for export] *)
  name_sp sp (-2128).
  eapply evtF_cut.
  { eapply (put_tail_spec ek g t hm lst RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 n nb fst0 qb b1 actx lo sjunk).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => rewrite Hsp; exact STf
         | |- mem_inv _ _ => exact MIf
         | |- poison_cells _ => exact PC1
         | |- ek_pre _ _ _ _ _ _ _ _ => exact EK1
         | |- dk_pre _ _ _ _ _ _ _ _ => exact DK1
         | |- @eq word _ _ => rewrite ?Esp; first [reflexivity | apply Z_to_bv_eqm; rewrite ?unsigned_lit by lia; lia]
         | |- _ \/ _ => ub DHT; ylia
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD1
         | |- rw_cells _ _ (shad _) _ => exact SH
         | |- rw_cells _ _ (_ + 80) _ => exact QC
         | |- iclr _ _ => exact TI
         end.
    all: try eassumption. all: try (unfold AIMG_HI, Q_MAX in *; lia).
    all: match goal with |- ?G => idtac "REMP" G end. }
  cbv beta. intros ms2 PP. unfold put_tail_post in PP.
  (nd_pre PP 17%nat; intros t0b t1b t2b a0b a1b a2b a3b a4b a5b a6b a7b t3b t4b t5b t6b m2 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 9%nat; intros MUp WMp MIp STp SH2 HD2 QC2 EKP DKP; nd_post).
  unname_sp. rewrite ?unsigned_lit in MUp by lia. rewrite ?unsigned_lit in STp by lia.
  replace (ret_pc (Z_to_bv 64 353068)) with (Z_to_bv 64 353068) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  (* [comment removed for export] *)
  xport FC1 MUp WMp ltac:(ub DHT; ub PF1; ub PF2; ub DF1; ylia).
  xport STATS1 MUp WMp ltac:(rewrite LSJ1; ub PF3; ub PF4; ub DF2; ylia).
  xport UW1 MUp WMp ltac:(ub PF3; ub PF4; ub DF2; ylia).
  xport FL1 MUp WMp ltac:(ub PL2; ub DG2; ylia). xport IAS1 MUp WMp ltac:(ub PL2; ub DG2; ylia).
  xport SS1 MUp WMp ltac:(lia). xport TB1 MUp WMp ltac:(rewrite LTB1; lia). xport FRS1 MUp WMp ltac:(lia).
  assert (IAM2 : forall j, 0 <= j < 32768 -> bytes_at asegs m2 (0xaf808 + 8 * j) (le8 (Z_to_bv 64 0))).
  { (intros j Hj; eapply bytes_at_agree; [exact (IAM1 j Hj)|];
    intros i Hi; apply MUp; cbn [outside]; rewrite length_le8 in Hi; rewrite wa_unsigned by lia; ub PL2; ub DG2; ylia). }
  clear IAM1.
  assert (DEP2 : ADEPOT DI L m2).
  { eapply (adi_frame DI); [exact DEP1 | exact MUp | exact WMp |].
    ((first [ apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [ lia |lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] | first [ apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [ lia |lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] | first [ apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [ ub DTN; ub DTS; ylia |lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] | first [ apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [ ub DTN; ub DTS; ylia |lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] | first [ apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [ ub DTN; ub DTS; ylia |lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] | first [ apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [ ub PF5; ub PF6; ub PL2; ylia |lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] | first [ apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [ ub PF7; ub PF8; ylia |lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] | first [ apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [ lia |lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] | first [ apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [ lia |lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] | first [ apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [ ub DF3; ub DF4; ub DG2; ylia |lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] |])] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] |]) ]); apply Forall_nil). }
  clear DEP1.
  (* [comment removed for export] *)
  apply rw_cells_of_u64arr in TB1. rewrite LTB1 in TB1.
  eapply evtF_mono.
  { (eapply (ficptD_spec RNG sp gp tp); [exact STp | atop_facts; lia | lia | exact MIp
      | eexists; split; [exact SS1 | reflexivity]
      | eexists; split; [replace (bv_unsigned sp + -2112) with (bv_unsigned sp + -2128 + 16) by lia; exact TB1 | reflexivity]
      | exact FRS1 | exact RIMG | exact RTLS | solve_rng ]). }
  cbv beta. intros ms3 [-> ST3].
  (* [comment removed for export] *)
  assert (MU : munch (free_W L sp t hm n lst ek g) m m2).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUp]].
    eapply munch_weaken; [| exact MUf].
    all: solve_sub_fp sp. }
  assert (WM : wmono asegs m m2) by (eapply wmono_trans; [exact WMf| exact WMp]).
  unfold free_fast_post. exists id. do 15 eexists. exists m2, sj1.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MIp|]. split; [exact ST3|]. split; [exact IDR|].
  split; [exact HD2|]. split; [exact FC1|]. split; [exact SH2|]. split; [exact QC2|]. split; [exact EKP|]. split; [exact DKP|].
  split; [exact STATS1|]. split; [exact LSJ1|]. split; [exact UW1|]. split; [exact FL1|]. split; [exact IAS1|]. split; [exact IAM2|].
  exact DEP2.
  Unshelve. all: try exact STf; try exact STp.
Qed.
End Zd1.
#[using="Type"] Lemma free_fast_spec : ltac:(let t := eval cbv delta [free_fast_spec__stmt] in free_fast_spec__stmt in exact t).
Proof. exact free_fast_spec__body. Qed.
End WithDepot.
End CANSEC2.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_afree_iseg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_front.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tail.TwB.
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
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.
(* [comment removed for export] *)
Local Ltac qlia := first [ LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                         | LiaTuning.zify_prune; Zify.zify; xlia zchecker ].
Local Ltac leaf2 := first [ left; qlia | right; qlia | qlia ].
Local Ltac band_leaf :=
  first [ leaf2
        | match goal with B : sclr ?a _ |- context [?a] =>
            let B' := fresh "BB" in pose proof B as B'; unfold sclr, KLS in B'; destruct B' as [B'|B']; leaf2 end
        | match goal with B : iclr ?a _ |- context [?a] =>
            let B' := fresh "BB" in pose proof B as B'; unfold iclr, AIMG_LO, AIMG_HI in B'; destruct B' as [_ [B'|B']]; leaf2 end
        | match goal with B : ablk ?a _ |- context [?a] =>
            let B' := fresh "BB" in pose proof B as B'; unfold ablk, KLS, AIMG_HI in B'; destruct B' as [[? B']|[B' ?]]; leaf2 end
        | lia ].
Local Ltac band_disj := cbn [disjoint_from fst snd]; repeat match goal with |- _ /\ _ => split end; first [exact I | band_leaf].
(* [comment removed for export] *)
Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6307840 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6307840 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (sclr_int a n H G1 G2) 4%nat; intros k A B C; nd_post); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (iclr_int a n H G2) 5%nat; intros k A B C D; nd_post); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>      (* [comment removed for export] *)
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (iclr_int a n H G2) 5%nat; intros k A B C D; nd_post); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.


Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
#[using="Type"] Lemma rw_cells_of_u64arr : forall m A ws,
  u64arr asegs m A ws -> rw_cells asegs m A [CB (8 * length ws) (u64s ws)].
Proof.
  intros m A ws [B W]. split; [split|].
  - cbn. split; [apply u64s_length| exact I].
  - cbn [cells_bytes cbytes app]. rewrite app_nil_r. exact B.
  - cbn [cells_size csize Nat.add]. replace (Z.of_nat (8 * length ws + 0)) with (8 * Z.of_nat (length ws)) by lia. exact W.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma poison_cells_frame2 : forall m m' W,
  poison_cells m -> munch W m m' -> wmono asegs m m' ->
  Forall (fun iv => 0x1405a8 <= fst iv \/ (0xaf6fc <= fst iv /\ snd iv <= 0x1405a0) \/ snd iv <= 0xa5880) W -> poison_cells m'.   (* [comment removed for export] *)
Proof.
  intros m m' W PC MU WM HW.
  assert (D : forall A n, 0xa5880 <= A -> (A + n <= 0xaf6fc \/ (0x1405a0 <= A /\ A + n <= 0x1405a8)) -> disjoint_from W A n).
  { intros A n HA HB. clear MU. induction HW as [|[lo hi] W H1 H2 IH]; cbn in *; [exact I|]. split; [lia| exact IH]. }
  unfold poison_cells in *.
  (nd_pre PC 7%nat; intros P1 P2 P3 P4 P5 P6 P7; nd_post).
  repeat split; (eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply D; cbn; lia]).
Qed.

(* [comment removed for export] *)
Definition ek_seps (ek : enq_kind) (L : alayout) (hm lst : Z) : Prop :=
  match ek with
  | EkAppend _ _ _ _ _ _ _ _ =>
         (hm + 24 <= lst \/ lst + 8192 <= hm)
      /\ (al_nodes L + 1048576 <= lst \/ lst + 8192 <= al_nodes L) /\ (al_store L + 8388608 <= lst \/ lst + 8192 <= al_store L)
  | EkNew full _ _ _ _ _ _ _ _ _ b _ =>
         (hm + 24 <= b \/ b + 8192 <= hm)
      /\ (al_nodes L + 1048576 <= b \/ b + 8192 <= al_nodes L) /\ (al_store L + 8388608 <= b \/ b + 8192 <= al_store L)
      /\ (full = true ->
             (hm + 24 <= lst \/ lst + 8192 <= hm)
          /\ (al_nodes L + 1048576 <= lst \/ lst + 8192 <= al_nodes L) /\ (al_store L + 8388608 <= lst \/ lst + 8192 <= al_store L))
  end.

Definition dk_seps (g : gqd) (L : alayout) (hm : Z) : Prop :=
  g_drain g = true -> g_full g = true ->
     (hm + 24 <= g_lst g \/ g_lst g + 8 <= hm)
  /\ (al_nodes L + 1048576 <= g_lst g \/ g_lst g + 8192 <= al_nodes L) /\ (al_store L + 8388608 <= g_lst g \/ g_lst g + 8192 <= al_store L).

(* [comment removed for export] *)
#[using="Type"] Lemma ek_pre_pure : forall ek RNG L t nb lst n hm m,
  ek_pre ek RNG t nb lst n hm m -> ek_seps ek L hm lst ->
  iclr t 4096 -> AIMG_HI <= hm -> AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L ->
     (hm + 24 <= lst \/ lst + 8192 <= hm) /\ (hm + 24 <= ek_b ek lst \/ ek_b ek lst + 8192 <= hm)
  /\ (t + 4096 <= lst \/ lst + 8192 <= t \/ lst = 0) /\ (t + 4096 <= ek_b ek lst \/ ek_b ek lst + 8192 <= t)
  /\ (al_nodes L + 1048576 <= lst \/ lst + 8192 <= al_nodes L) /\ (al_store L + 8388608 <= lst \/ lst + 8192 <= al_store L)
  /\ (al_nodes L + 1048576 <= ek_b ek lst \/ ek_b ek lst + 8192 <= al_nodes L) /\ (al_store L + 8388608 <= ek_b ek lst \/ ek_b ek lst + 8192 <= al_store L)
  /\ 0 <= lst /\ lst + 8192 <= ATOP /\ 0 <= ek_b ek lst /\ ek_b ek lst + 8192 <= ATOP
  /\ (lst = 0 \/ 0x10007fff8000 <= lst) /\ 0x10007fff8000 <= ek_b ek lst.
Proof.
  intros ek RNG L t nb lst n hm m EK ES T0 H0 N0 R0. unfold AIMG_HI in *. band_lin.   (* [comment removed for export] *)
  destruct ek as [nx bsz cnt hs cnt24' maxc' csz' stj' | full nx bsz cnt24 maxc csz stj idxw chunks spacebeg b hs0]; cbn [ek_pre ek_seps ek_b] in *.
  - (nd_pre EK 16%nat; intros NB1 LB CNT BSZ BSZN NX LA LEN LJ L0 L1 DTL DHL CR' STS' RL; nd_post). atop_facts. lia.
  - (nd_pre EK 20%nat; intros FULL SB CR CH LCH CNT NTH IXS STS HB BJ SBP B0 BL1 DTB DTL DBL DHB DHL RB; nd_post).
    (nd_pre ES 4%nat; intros S1 S2 S3 S4; nd_post). atop_facts.
    destruct full; [(nd_pre FULL 9%nat; intros NB1 LB NX BSZ L0 L1 LA0 LEN0 RL; nd_post); specialize (S4 eq_refl) | destruct FULL as [NB0 LST0]]; lia.
Qed.

#[using="Type"] Lemma dk_pre_pure : forall ek g RNG L t lst hm qb' m,
  dk_pre ek g RNG t lst hm qb' m -> dk_seps g L hm ->
  iclr t 4096 -> AIMG_HI <= hm -> AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L ->
  (hm + 24 <= lst \/ lst + 8192 <= hm) -> (t + 4096 <= lst \/ lst + 8192 <= t \/ lst = 0) ->
  (al_nodes L + 1048576 <= lst \/ lst + 8192 <= al_nodes L) -> (al_store L + 8388608 <= lst \/ lst + 8192 <= al_store L) ->
  0 <= lst -> lst + 8192 <= ATOP -> (lst = 0 \/ 0x10007fff8000 <= lst) ->
     (hm + 24 <= dk_glst g lst \/ dk_glst g lst + 8 <= hm) /\ (t + 4096 <= dk_glst g lst \/ dk_glst g lst + 8 <= t)
  /\ (al_nodes L + 1048576 <= dk_glst g lst \/ dk_glst g lst + 8 <= al_nodes L) /\ (al_store L + 8388608 <= dk_glst g lst \/ dk_glst g lst + 8 <= al_store L)
  /\ 0 <= dk_glst g lst /\ dk_glst g lst + 8 <= ATOP /\ (dk_glst g lst = 0 \/ 0x10007fff8000 <= dk_glst g lst).
Proof.
  intros ek g RNG L t lst hm qb' m DK DS T0 H0 N0 R0 P1 P3 P5 P6 LNN LHI LZH. unfold AIMG_HI in *. band_lin.   (* [comment removed for export] *)
  unfold dk_pre, dk_seps, dk_glst in *.
  (nd_pre DK 7%nat; intros MX GC GNB GQB GFST GLST DK'; nd_post).
  destruct (g_drain g); [| lia].
  (nd_pre DK' 3%nat; intros QB1 GQ GFULL; nd_post).
  destruct (g_full g); [(nd_pre GFULL 9%nat; intros G1 GLB G3 G4 G5 G6 G7 G8 G9; nd_post); specialize (DS eq_refl eq_refl) | destruct GFULL as [GNB0 GLST0]];
    atop_facts; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma outside_In : forall W x jv, outside W x -> In jv W -> ~ (fst jv <= x < snd jv).
Proof.
  induction W as [|[lo hi] W IH]; cbn; intros x jv Ho Hin; [tauto|].
  destruct Ho as [H1 H2]. destruct Hin as [<-|Hin]; [exact H1| exact (IH _ _ H2 Hin)].
Qed.
#[using="Type"] Lemma sub_fp_by_incl : forall W W',
  Forall (fun iv => Exists (fun jv => fst jv <= fst iv /\ snd iv <= snd jv) W') W -> sub_fp W W'.
Proof.
  intros W W' HF x Ho. induction HF as [|[lo hi] W HE HF IH]; cbn; [exact I|].
  split; [| exact IH]. apply Exists_exists in HE. (nd_pre HE 4%nat; intros jv Hin H1 H2; nd_post). cbn in H1, H2.
  pose proof (outside_In W' x jv Ho Hin). lia.
Qed.
(* [comment removed for export] *)
End CANSEC1.
Ltac find_iv s :=
  first [ apply Exists_cons_hd; cbn [fst snd]; split; apply Z.le_refl
        | apply Exists_cons_hd; cbn [fst snd]; solve [clear - s; lia]
        | apply Exists_cons_tl; find_iv s ].
Ltac solve_sub_fp s :=
  apply sub_fp_by_incl; repeat (apply Forall_cons; [find_iv s|]); apply Forall_nil.

(* [comment removed for export] *)
Ltac reasm :=
  repeat (lazymatch goal with
          | |- rng _ _ _ => assumption
          | |- ex _ => eexists; eassumption
          | |- _ /\ _ => first [assumption | split; [first [assumption | lia | eexists; eassumption] | ]]
          | |- _ => first [assumption | lia | exact I]
          end).

Section CANSEC2. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section Transport.
(* [comment removed for export] *)
Variables (L : alayout) (sp : word) (t hm lo : Z) (m m' : amem).
Hypothesis MU : munch [(bv_unsigned sp - 4096, bv_unsigned sp); (0xafc00, 0xafc00 + 0x81030); (0x13e488, 0x13e488 + 4);
    (t + 3168, t + 3169); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368);
    (0x1808c8, 0x5d0910); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z m m'.
Hypothesis WM : wmono asegs m m'.
Hypotheses (CEIL : ATOP <= lo) (LO : lo <= bv_unsigned sp - 4096) (T0 : iclr t 4096) (T1 : t + 4096 <= ATOP)     (* [comment removed for export] *)
           (H0 : AIMG_HI <= hm) (DHT : hm + 24 <= t \/ t + 4096 <= hm) (N0 : AIMG_HI <= al_nodes L) (R0 : AIMG_HI <= al_store L)
           (DTN : t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) (DTS : t + 4096 <= al_store L \/ al_store L + 8388608 <= t).

#[using="sp lo MU WM CEIL LO T0 T1 H0 DHT N0 R0 DTN DTS"] Lemma ek_pre_front : forall ek RNG nb lst n,
  ek_pre ek RNG t nb lst n hm m -> ek_seps ek L hm lst -> ek_pre ek RNG t nb lst n hm m'.
Proof.
  intros ek RNG nb lst n EK ES. unfold AIMG_HI in *. band_lin.   (* [comment removed for export] *)
  destruct ek as [nx bsz cnt hs cnt24' maxc' csz' stj' | full nx bsz cnt24 maxc csz stj idxw chunks spacebeg b hs0]; cbn [ek_pre ek_seps] in *.
  - (nd_pre EK 16%nat; intros NB1 LB CNT BSZ BSZN NX LA LEN [junkt LJ] L0 L1 DTL DHL CR' STS' RL; nd_post). atop_facts.
    (nd_pre ES 3%nat; intros S1 S2 S3; nd_post).
    xport LB MU WM ltac:(clear -CEIL LO T0 T1 H0 DHT N0 R0 DTN DTS L0 L1 DTL DHL S1 S2 S3; lia). xport LA MU WM ltac:(rewrite LEN; clear -CEIL LO T0 T1 H0 DHT N0 R0 DTN DTS L0 L1 DTL DHL CNT S1 S2 S3; lia). xport LJ MU WM ltac:(clear -CEIL LO T0 T1 H0 DHT N0 R0 DTN DTS L0 L1 DTL DHL CNT S1 S2 S3; lia).   (* [comment removed for export] *)
    xport CR' MU WM ltac:(clear -CEIL LO T0 T1 H0 DHT N0 R0 DTN DTS; lia). xport STS' MU WM ltac:(clear -CEIL LO T0 T1 H0 DHT N0 R0 DTN DTS; lia).
    reasm.
  - (nd_pre EK 20%nat; intros FULL SB CR CH LCH CNT NTH IXS STS HB [junkb BJ] SBP B0 BL1 DTB DTL DBL DHB DHL RB; nd_post).
    (nd_pre ES 4%nat; intros S1 S2 S3 S4; nd_post). atop_facts.
    xport SB MU WM ltac:(clear -CEIL LO T0 T1 H0 DHT N0 R0 DTN DTS; lia). xport CR MU WM ltac:(clear -CEIL LO T0 T1 H0 DHT N0 R0 DTN DTS; lia). xport CH MU WM ltac:(rewrite LCH; clear -CEIL LO T0 T1 H0 DHT N0 R0 DTN DTS; lia). xport STS MU WM ltac:(clear -CEIL LO T0 T1 H0 DHT N0 R0 DTN DTS; lia). xport BJ MU WM ltac:(clear -CEIL LO T0 T1 H0 DHT N0 R0 DTN DTS B0 BL1 DTB DHB S1 S2 S3; lia).
    split.
    + destruct full; [| exact FULL]. (nd_pre FULL 9%nat; intros NB1 LB NX BSZ L0 L1 LA0 LEN0 RL; nd_post). specialize (S4 eq_refl). (nd_pre S4 3%nat; intros S5 S6 S7; nd_post).
      xport LB MU WM ltac:(clear -CEIL LO T0 T1 H0 DHT N0 R0 DTN DTS L0 L1 DTL DHL S5 S6 S7; lia). xport LA0 MU WM ltac:(rewrite LEN0; clear -CEIL LO T0 T1 H0 DHT N0 R0 DTN DTS L0 L1 DTL DHL S5 S6 S7; lia). reasm.
    + reasm.
Qed.

#[using="sp lo MU WM CEIL LO T0 T1 H0 DHT N0 R0 DTN DTS"] Lemma dk_pre_front : forall ek g RNG lst qb',
  dk_pre ek g RNG t lst hm qb' m -> dk_seps g L hm -> dk_pre ek g RNG t lst hm qb' m'.
Proof.
  intros ek g RNG lst qb' DK DS. unfold AIMG_HI in *. band_lin.   (* [comment removed for export] *)
  unfold dk_pre, dk_seps in *.
  (nd_pre DK 7%nat; intros MX GC GNB GQB GFST GLST DK'; nd_post).
  xport MX MU WM ltac:(lia). xport GC MU WM ltac:(lia).
  do 6 (split; [assumption|]).
  destruct (g_drain g); [| exact DK'].
  (nd_pre DK' 3%nat; intros QB1 GQ GFULL; nd_post). split; [exact QB1|]. split; [exact GQ|].
  destruct (g_full g); [| exact GFULL].
  (nd_pre GFULL 9%nat; intros G1 GLB G3 G4 G5 G6 G7 G8 G9; nd_post). specialize (DS eq_refl eq_refl). (nd_pre DS 3%nat; intros D1 D2 D3; nd_post). atop_facts.
  xport GLB MU WM ltac:(lia). reasm.
Qed.
End Transport.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithDepot.
Variable DI : ADepotIface.

Notation free_W L sp t hm n lst ek g :=
  ([(bv_unsigned sp - 4096, bv_unsigned sp); (0xafc00, 0xafc00 + 0x81030); (0x13e488, 0x13e488 + 4);
    (t + 3168, t + 3169); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608);
    (shad (hm + 16), shad (hm + 16) + shlen (rup n 8)); (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792);
    (lst, lst + qsz lst); (ek_b ek lst, ek_b ek lst + 8192);
    (0xab708, 0xab708 + 4); (0xab710, 0xab710 + 32); (dk_glst g lst, dk_glst g lst + 8)]%Z) (only parsing).

Definition free_fast_post (L : alayout) (ek : enq_kind) (g : gqd)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t hm n nb fst0 lst qb b1 actx lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (id : Z) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m' (sj' : list word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (free_W L sp t hm n lst ek g) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ 0 < id < 2^31
    /\ rw_cells asegs m' hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)]
    /\ rw_cells asegs m' (hm + 16) [C8 (Z_to_bv 64 id)]
    /\ rw_cells asegs m' (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) (repeat (Z_to_bv 8 253) (Z.to_nat (shlen (rup n 8))))]
    /\ rw_cells asegs m' (t + 80) (tcache_post g (ek_nb ek nb) (ek_fst ek fst0) (ek_lst ek lst) (qb + ek_delta ek n))
    /\ ek_post ek t lst hm n m'
    /\ dk_post g (ek_nb ek nb) (ek_fst ek fst0) (ek_lst ek lst) (qb + ek_delta ek n) m'
    /\ u64arr asegs m' (t + 2800) sj' /\ length sj' = 46%nat
    /\ rw_cells asegs m' (t + 3168) [C1 (Z_to_bv 8 0)]
    /\ rw_cells asegs m' 0x13e488 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ stk asegs m' 0xafc00 (0xafc00 + 0x81030)
    /\ (forall j, 0 <= j < 32768 -> bytes_at asegs m' (0xafc08 + 8 * j) (le8 (Z_to_bv 64 0)))
    /\ ADEPOT DI L m'.

Definition free_fast_spec__stmt : Prop := forall (L : alayout) (ia : bool) (ek : enq_kind) (g : gqd) RNG
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem)
    (t ctx hm n b1 actx lo top bot nb fst0 lst qb : Z) (uw : word) (sj : list word) (sjunk : list byte) (trt : list Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 (hm + 16) ->
  bv_unsigned sp mod 16 = 0 ->
  (* [comment removed for export] *)
  allocA_cells m ctx t -> poison_cells m ->
  rw_cells asegs m 0xaf6fc [C4 (Z_to_bv 64 30)] ->
  rw_cells asegs m 0x14054a [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m 0xa5870 [C8 (Z_to_bv 64 0x13e4a0)] -> rw_cells asegs m 0x13e4a0 [C8 (Z_to_bv 64 4096)] ->
  rw_cells asegs m 0x1404c8 [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m 0xab6b0 [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->
  rw_cells asegs m 0xa5888 [C8 (Z_to_bv 64 AFLAGS)] ->
  rw_cells asegs m 0xac224 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->
  (* [comment removed for export] *)
  rw_cells asegs m 0x13e488 [C1 (Z_to_bv 8 (if ia then 1 else 0)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  stk asegs m 0xafc00 (0xafc00 + 0x81030) ->
  (ia = true -> forall j, 0 <= j < 32768 -> bytes_at asegs m (0xafc08 + 8 * j) (le8 (Z_to_bv 64 0))) ->
  (* [comment removed for export] *)
  rw_cells asegs m (ctx + 8) [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m t [C8 (Z_to_bv 64 ctx); C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)] ->
  rw_cells asegs m (t + 40) [C1 (Z_to_bv 8 0)] -> rw_cells asegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  rw_cells asegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= qb -> qb + n + 8192 < 2^62 -> 0 <= fst0 < 2^64 -> 0 <= lst < 2^64 ->
  0 < ctx -> sclr ctx 65536 -> ctx + 4096 <= ATOP ->
  sclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> t mod 4096 = 0 -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  (* [comment removed for export] *)
  rw_cells asegs m hm [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  rw_cells asegs m (hm + 16) [C8 uw] -> 0 <= b1 < 256 -> Z.land b1 3 = 1 -> 1 <= n <= Q_MAX -> hm mod 16 = 0 ->
  ablk hm (hm + 16 + rup n 8) -> tclr hm 24 -> hm + 16 + rup n 8 <= ATOP -> hm + 24 <= ATOP ->
  rw_cells asegs m (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) sjunk] ->
  (hm + 24 <= t \/ t + 4096 <= hm) -> (hm + 24 <= ctx \/ ctx + 4096 <= hm) ->
  (* [comment removed for export] *)
  ek_pre ek RNG t nb lst n hm m -> ek_seps ek L hm lst ->
  dk_pre ek g RNG t lst hm (qb + ek_delta ek n) m -> dk_seps g L hm ->
  (* [comment removed for export] *)
  ADEPOT DI L m ->
  sclr (al_nodes L) 1048576 -> al_nodes L + 1048576 <= ATOP -> sclr (al_store L) 8388608 -> al_store L + 8388608 <= ATOP ->
  (hm + 24 <= al_nodes L \/ al_nodes L + 1048576 <= hm) -> (hm + 24 <= al_store L \/ al_store L + 8388608 <= hm) ->
  (t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) -> (t + 4096 <= al_store L \/ al_store L + 8388608 <= t) ->
  (ctx + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= ctx) -> (ctx + 4096 <= al_store L \/ al_store L + 8388608 <= ctx) -> tclr (al_nodes L) 1048576 -> tclr (al_store L) 8388608 ->
  (* [comment removed for export] *)
  afree_unw RNG lo m top sp s0 ra trt ->
  bv_unsigned s0 <> bv_unsigned sp + 8 ->
  In (AFREE_PC :: trt) (al_U L) ->
  0 <= bot -> bot < bv_unsigned sp -> bot < top -> 4096 <= top <= 2^47 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 -> rng RNG hm 24 -> rng RNG (shad (hm + 16)) (shlen (rup n 8)) ->
  AIMG_HI <= ctx -> AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L -> iclr t 4096 ->      (* [comment removed for export] *)
  evtF asegs RNG (free_fast_post L ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n nb fst0 lst qb b1 actx lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 0).
Variable ia : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 1).
Variable ek : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 2).
Variable g : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 3).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 4).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 5).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 6).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 7).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 8).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 9).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 10).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 11).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 12).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 13).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 14).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 15).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 16).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 17).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 18).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 19).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 20).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 21).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 22).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 23).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 24).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 25).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 26).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 27).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 28).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 29).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 30).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 31).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 32).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 33).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 34).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 35).
Variable F : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 36).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 37).
Variable m : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 38).
Variable t : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 39).
Variable ctx : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 40).
Variable hm : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 41).
Variable n : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 42).
Variable b1 : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 43).
Variable actx : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 44).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 45).
Variable top : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 46).
Variable bot : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 47).
Variable nb : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 48).
Variable fst0 : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 49).
Variable lst : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 50).
Variable qb : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 51).
Variable uw : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 52).
Variable sj : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 53).
Variable sjunk : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 54).
Variable trt : ltac2:(SecDietF.SzSecF.ty 'free_fast_spec__stmt 55).
#[using="Type"] Lemma free_fast_spec__body : ltac:(let T := type of (fun (h : free_fast_spec__stmt) => h L ia ek g RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m t ctx hm n b1 actx lo top bot nb fst0 lst qb uw sj sjunk trt) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (ia, (ek, (g, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (t, (ctx, (hm, (n, (b1, (actx, (lo, (top, (bot, (nb, (fst0, (lst, (qb, (uw, (sj, (sjunk, trt)))))))))))))))))))))))))))))))))))))))))))))))))))))))) as _.

  intros ST CEIL LO MI TP Ha0 SP16 AC PC MCS CF34 GPG PGC HK QK GF FLG FL IAS IAM CT8 TT0 SW UW STATS LSJ QC NB QB QBN FST LST
         CX0 C0 C1 T0 T1 TAL CT2 HD HUW B1 B13 N AL HLO TCH HHI HCE SH DHT DHC EK ES DK DS DEP N0 N1 R0 R1 DHN DHS DTN DTS DCN DCS XTNO XTST
         UNW S0NE TRU B0 BB BOTOP TOP RA4 RANE RIMG RTLS RSTK RCTX RT RNO RST RH RSH CI NI SI TI.
  band_int TI. (pose proof (ablk_lin _ _ HLO) as ndP__; nd_pre ndP__ 4%nat; intros HL1 HL2 HL3 HL4; nd_post). unfold AIMG_HI in HL1. band_int HLO. band_lin. band_int C0. band_int T0. band_int N0. band_int R0.   (* [comment removed for export] *)
  pose proof (afree_unw_length _ _ _ _ _ _ _ _ UNW) as LTRT.
  pose proof (afree_unw_sp47 _ _ _ _ _ _ _ _ UNW ltac:(clear -TOP; lia)) as SP47.
  pose proof PC as PC'. destruct PC' as (GOT6 & _).
  assert (RUP : n <= rup n 8 <= n + 7 /\ rup n 8 mod 8 = 0) by (clear -N; unfold rup; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
  assert (SHB : 2148239360 <= shad (hm + 16) /\ shad (hm + 16) + shlen (rup n 8) <= 0x10007fff8000 /\ 0 < shlen (rup n 8)).
  { clear -N HLO HL1 HHI HCE. atop_facts. unfold shad, shlen, ASHOFF, rup in *. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold Q_MAX in *. Z.div_mod_to_equations. lia. }
  (pose proof (ek_pre_pure ek RNG L t nb lst n hm m EK ES TI ltac:(unfold AIMG_HI; lia) NI SI) as ndP__; nd_pre ndP__ 14%nat; intros PF1 PF2 PF3 PF4 PF5 PF6 PF7 PF8 PL0 PL1 PB0 PB1 PL2 PB2; nd_post).
  (pose proof (dk_pre_pure ek g RNG L t lst hm (qb + ek_delta ek n) m DK DS TI ltac:(unfold AIMG_HI; lia) NI SI PF1 PF3 PF5 PF6 PL0 PL1 PL2) as ndP__; nd_pre ndP__ 7%nat; intros DF1 DF2 DF3 DF4 DG0 DG1 DG2; nd_post).
  (pose proof (qsz_int lst PL0 ltac:(clear -PL1; atop_facts; lia)) as ndP__; nd_pre ndP__ 5%nat; intros zq QZ0 QZ1 QZ2 QZ3; nd_post).   (* [comment removed for export] *)
  unfold AIMG_HI, AFREE_SYM, AFREE_PC in *.
  word_range sp SPR.
  box DHT. box DHC. box DHN. box DHS. box DTN. box DTS. box DCN. box DCS. box CT2.
  box PF1. box PF2. box PF3. box PF4. box PF5. box PF6. box PF7. box PF8. box DF1. box DF2. box DF3. box DF4. box PL2. box DG2.
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (free_front_spec DI L ia RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
              t ctx hm n b1 actx lo top bot uw sj trt).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact ST | exact IAS]
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => exact AC
         | |- ADEPOT _ _ _ => exact DEP
         | |- afree_unw _ _ _ _ _ _ => exact UNW
         | |- In _ _ => exact TRU
         | |- u64arr _ _ _ _ => exact STATS
         | |- _ = true -> _ => exact IAM
         | |- _ \/ _ => first [unboxed DHT | unboxed DHC | unboxed DHN | unboxed DHS | unboxed DTN | unboxed DTS | unboxed DCN | unboxed DCS | unboxed CT2]
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _] => exact TT0
         | |- rw_cells _ _ (_ + 16) _ => exact HUW
         | |- rw_cells _ _ (_ + 8) _ => exact CT8
         | |- rw_cells _ _ (_ + 40) _ => exact SW
         | |- rw_cells _ _ (_ + 3168) _ => exact UW
         end.
    all: try eassumption. all: try (unfold AIMG_HI, Q_MAX in *; lia).
    all: match goal with |- ?G => idtac "REMF" G end. }
  cbv beta. intros ms1 PFR. unfold free_front_post in PFR.
  (nd_pre PFR 15%nat; intros id t0a t1a t2a a6a a7a t3a t4a t5a t6a m1 sj1 tb1 junk2 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 18%nat; intros MUf WMf MIf STf IDR HD1 FC1 STATS1 LSJ1 UW1 FL1 IAS1 IAM1 SS1 TB1 LTB1 FRS1 DEP1; nd_post).
  (* [comment removed for export] *)
  xport QK MUf WMf ltac:(lia). xport GF MUf WMf ltac:(lia). xport FLG MUf WMf ltac:(lia).
  xport QC MUf WMf ltac:(ub DHT; ub DTN; ub DTS; ylia).
  xport SH MUf WMf ltac:(band_disj).   (* [comment removed for export] *)
  assert (PC1 : poison_cells m1).
  { eapply poison_cells_frame2; [exact PC | exact MUf | exact WMf |].
    repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
  assert (EK1 : ek_pre ek RNG t nb lst n hm m1).
  { eapply (ek_pre_front L sp t hm lo m m1); [exact MUf | exact WMf | ..]; try (unfold AIMG_HI; lia).
    all: first [exact TI | unboxed DHT | unboxed DTN | unboxed DTS | exact EK | exact ES]. }
  assert (DK1 : dk_pre ek g RNG t lst hm (qb + ek_delta ek n) m1).
  { eapply (dk_pre_front L sp t hm lo m m1); [exact MUf | exact WMf | ..]; try (unfold AIMG_HI; lia).
    all: first [exact TI | unboxed DHT | unboxed DTN | unboxed DTS | exact DK | exact DS]. }
  clear EK DK PC.
  (* [comment removed for export] *)
  name_sp sp (-2128).
  eapply evtF_cut.
  { eapply (put_tail_spec ek g t hm lst RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 n nb fst0 qb b1 actx lo sjunk).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => rewrite Hsp; exact STf
         | |- mem_inv _ _ => exact MIf
         | |- poison_cells _ => exact PC1
         | |- ek_pre _ _ _ _ _ _ _ _ => exact EK1
         | |- dk_pre _ _ _ _ _ _ _ _ => exact DK1
         | |- @eq word _ _ => rewrite ?Esp; first [reflexivity | apply Z_to_bv_eqm; rewrite ?unsigned_lit by lia; lia]
         | |- _ \/ _ => ub DHT; ylia
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD1
         | |- rw_cells _ _ (shad _) _ => exact SH
         | |- rw_cells _ _ (_ + 80) _ => exact QC
         | |- iclr _ _ => exact TI
         end.
    all: try eassumption. all: try (unfold AIMG_HI, Q_MAX in *; lia).
    all: match goal with |- ?G => idtac "REMP" G end. }
  cbv beta. intros ms2 PP. unfold put_tail_post in PP.
  (nd_pre PP 17%nat; intros t0b t1b t2b a0b a1b a2b a3b a4b a5b a6b a7b t3b t4b t5b t6b m2 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 9%nat; intros MUp WMp MIp STp SH2 HD2 QC2 EKP DKP; nd_post).
  unname_sp. rewrite ?unsigned_lit in MUp by lia. rewrite ?unsigned_lit in STp by lia.
  replace (ret_pc (Z_to_bv 64 353172)) with (Z_to_bv 64 353172) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  (* [comment removed for export] *)
  xport FC1 MUp WMp ltac:(ub DHT; ub PF1; ub PF2; ub DF1; ylia).
  xport STATS1 MUp WMp ltac:(rewrite LSJ1; ub PF3; ub PF4; ub DF2; ylia).
  xport UW1 MUp WMp ltac:(ub PF3; ub PF4; ub DF2; ylia).
  xport FL1 MUp WMp ltac:(ub PL2; ub DG2; ylia). xport IAS1 MUp WMp ltac:(ub PL2; ub DG2; ylia).
  xport SS1 MUp WMp ltac:(lia). xport TB1 MUp WMp ltac:(rewrite LTB1; lia). xport FRS1 MUp WMp ltac:(lia).
  assert (IAM2 : forall j, 0 <= j < 32768 -> bytes_at asegs m2 (0xafc08 + 8 * j) (le8 (Z_to_bv 64 0))).
  { (intros j Hj; eapply bytes_at_agree; [exact (IAM1 j Hj)|];
    intros i Hi; apply MUp; cbn [outside]; rewrite length_le8 in Hi; rewrite wa_unsigned by lia; ub PL2; ub DG2; ylia). }
  clear IAM1.
  assert (DEP2 : ADEPOT DI L m2).
  { eapply (adi_frame DI); [exact DEP1 | exact MUp | exact WMp |].
    ((first [ apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [ lia |lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] | first [ apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [ lia |lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] | first [ apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [ ub DTN; ub DTS; ylia |lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] | first [ apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [ ub DTN; ub DTS; ylia |lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] | first [ apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [ ub DTN; ub DTS; ylia |lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] | first [ apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [ ub PF5; ub PF6; ub PL2; ylia |lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] | first [ apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [ ub PF7; ub PF8; ylia |lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] | first [ apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [ lia |lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] | first [ apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [ lia |lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] | first [ apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [ ub DF3; ub DF4; ub DG2; ylia |lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] |])] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] |]) ]); apply Forall_nil). }
  clear DEP1.
  (* [comment removed for export] *)
  apply rw_cells_of_u64arr in TB1. rewrite LTB1 in TB1.
  eapply evtF_mono.
  { (eapply (ficptD_spec RNG sp gp tp); [exact STp | atop_facts; lia | lia | exact MIp
      | eexists; split; [exact SS1 | reflexivity]
      | eexists; split; [replace (bv_unsigned sp + -2112) with (bv_unsigned sp + -2128 + 16) by lia; exact TB1 | reflexivity]
      | exact FRS1 | exact RIMG | exact RTLS | solve_rng ]). }
  cbv beta. intros ms3 [-> ST3].
  (* [comment removed for export] *)
  assert (MU : munch (free_W L sp t hm n lst ek g) m m2).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUp]].
    eapply munch_weaken; [| exact MUf].
    all: solve_sub_fp sp. }
  assert (WM : wmono asegs m m2) by (eapply wmono_trans; [exact WMf| exact WMp]).
  unfold free_fast_post. exists id. do 15 eexists. exists m2, sj1.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MIp|]. split; [exact ST3|]. split; [exact IDR|].
  split; [exact HD2|]. split; [exact FC1|]. split; [exact SH2|]. split; [exact QC2|]. split; [exact EKP|]. split; [exact DKP|].
  split; [exact STATS1|]. split; [exact LSJ1|]. split; [exact UW1|]. split; [exact FL1|]. split; [exact IAS1|]. split; [exact IAM2|].
  exact DEP2.
  Unshelve. all: try exact STf; try exact STp.
Qed.
End Zd1.
#[using="Type"] Lemma free_fast_spec : ltac:(let t := eval cbv delta [free_fast_spec__stmt] in free_fast_spec__stmt in exact t).
Proof. exact free_fast_spec__body. Qed.
End WithDepot.
End CANSEC2.
End TwB.
End F_afree_icpt.

(* [comment removed for export] *)
Module F_adeallocfn_icpt.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecSlog__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_adrain__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_tail. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_afree_iseg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_front OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tail OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_icpt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_adeallocfn_front.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
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
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.
(* [comment removed for export] *)
Local Ltac qlia := first [ LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                         | LiaTuning.zify_prune; Zify.zify; xlia zchecker ].
Local Ltac leaf2 := first [ left; qlia | right; qlia | qlia ].
Local Ltac band_leaf :=
  first [ leaf2
        | match goal with B : sclr ?a _ |- context [?a] =>
            let B' := fresh "BB" in pose proof B as B'; unfold sclr, KLS in B'; destruct B' as [B'|B']; leaf2 end
        | match goal with B : iclr ?a _ |- context [?a] =>
            let B' := fresh "BB" in pose proof B as B'; unfold iclr, AIMG_LO, AIMG_HI in B'; destruct B' as [_ [B'|B']]; leaf2 end
        | match goal with B : ablk ?a _ |- context [?a] =>
            let B' := fresh "BB" in pose proof B as B'; unfold ablk, KLS, AIMG_HI in B'; destruct B' as [[? B']|[B' ?]]; leaf2 end
        | lia ].
Local Ltac band_disj := cbn [disjoint_from fst snd]; repeat match goal with |- _ /\ _ => split end; first [exact I | band_leaf].
(* [comment removed for export] *)
Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6303744 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} {tlsI : ABase.atlsT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6303744 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (sclr_int a n H G1 G2) 4%nat; intros k A B C; nd_post); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (iclr_int a n H G2) 5%nat; intros k A B C D; nd_post); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>      (* [comment removed for export] *)
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (iclr_int a n H G2) 5%nat; intros k A B C D; nd_post); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.


Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC2. Context {rc : runConstT} {tlsI : ABase.atlsT}.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithDepot.
Variable DI : ADepotIface.

Notation free_W L sp t hm n lst ek g :=
  ([(bv_unsigned sp - 4096, bv_unsigned sp); (0xaf800, 0xaf800 + 0x81030); (0x13e088, 0x13e088 + 4);
    (t + 3168, t + 3169); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608);
    (shad (hm + 16), shad (hm + 16) + shlen (rup n 8)); (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792);
    (lst, lst + qsz lst); (ek_b ek lst, ek_b ek lst + 8192);
    (0xab308, 0xab308 + 4); (0xab310, 0xab310 + 32); (dk_glst g lst, dk_glst g lst + 8)]%Z) (only parsing).

Definition dfn_fast_spec__stmt : Prop := forall (L : alayout) (ek : enq_kind) (g : gqd) RNG
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem)
    (t ctx hm n b1 actx lo nb fst0 lst qb S sz pc : Z) (uw top bot : word) (sj tb : list word) (sjunk : list byte) (trt : list Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 (hm + 16) -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 0 -> a4 = Z_to_bv 64 S -> a5 = Z_to_bv 64 1 ->
  (* [comment removed for export] *)
  allocA_cells m ctx t -> poison_cells m ->
  rw_cells asegs m 0xaf2fc [C4 (Z_to_bv 64 30)] ->
  rw_cells asegs m 0x14014a [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m 0xa5490 [C8 (Z_to_bv 64 0x13e0a0)] -> rw_cells asegs m 0x13e0a0 [C8 (Z_to_bv 64 4096)] ->
  rw_cells asegs m 0x1400c8 [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m 0xab2b0 [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->
  rw_cells asegs m 0xa54a8 [C8 (Z_to_bv 64 AFLAGS)] ->
  rw_cells asegs m 0xabe24 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->
  (* [comment removed for export] *)
  rw_cells asegs m 0x13e088 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  stk asegs m 0xaf800 (0xaf800 + 0x81030) ->
  (forall j, 0 <= j < 32768 -> bytes_at asegs m (0xaf808 + 8 * j) (le8 (Z_to_bv 64 0))) ->
  (* [comment removed for export] *)
  rw_cells asegs m (ctx + 8) [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m t [C8 (Z_to_bv 64 ctx); C8 top; C8 bot] ->
  rw_cells asegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  rw_cells asegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= qb -> qb + n + 8192 < 2^62 -> 0 <= fst0 < 2^64 -> 0 <= lst < 2^64 ->
  0 < ctx -> sclr ctx 65536 -> ctx + 4096 <= ATOP ->
  sclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> t mod 4096 = 0 -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  (* [comment removed for export] *)
  rw_cells asegs m hm [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  rw_cells asegs m (hm + 16) [C8 uw] -> 0 <= b1 < 256 -> Z.land b1 3 = 1 -> 1 <= n <= Q_MAX -> hm mod 16 = 0 ->
  ablk hm (hm + 16 + rup n 8) -> tclr hm 24 -> hm + 16 + rup n 8 <= ATOP -> hm + 24 <= ATOP ->
  rw_cells asegs m (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) sjunk] ->
  (hm + 24 <= t \/ t + 4096 <= hm) -> (hm + 24 <= ctx \/ ctx + 4096 <= hm) ->
  (* [comment removed for export] *)
  ek_pre ek RNG t nb lst n hm m -> ek_seps ek L hm lst ->
  dk_pre ek g RNG t lst hm (qb + ek_delta ek n) m -> dk_seps g L hm ->
  (* [comment removed for export] *)
  ADEPOT DI L m ->
  sclr (al_nodes L) 1048576 -> al_nodes L + 1048576 <= ATOP -> sclr (al_store L) 8388608 -> al_store L + 8388608 <= ATOP ->
  (hm + 24 <= al_nodes L \/ al_nodes L + 1048576 <= hm) -> (hm + 24 <= al_store L \/ al_store L + 8388608 <= hm) ->
  (t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) -> (t + 4096 <= al_store L \/ al_store L + 8388608 <= t) ->
  (ctx + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= ctx) -> (ctx + 4096 <= al_store L \/ al_store L + 8388608 <= ctx) -> tclr (al_nodes L) 1048576 -> tclr (al_store L) 8388608 ->
  (* [comment removed for export] *)
  rw_cells asegs m S [C8 (Z_to_bv 64 (S + 16)); C4 (Z_to_bv 64 sz); C4 (Z_to_bv 64 0)] ->
  u64arr asegs m (S + 16) tb -> length tb = 255%nat ->
  sz = 1 + Z.of_nat (length trt) -> sz <= 255 ->
  map bv_unsigned (firstn (Datatypes.S (length trt)) tb) = pc :: trt -> In (pc :: trt) (al_U L) ->
  bv_unsigned sp <= S -> S + 2056 <= 2^47 -> rng RNG S 2056 ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 -> rng RNG hm 24 -> rng RNG (shad (hm + 16)) (shlen (rup n 8)) ->
  AIMG_HI <= ctx -> AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L -> iclr t 4096 ->      (* [comment removed for export] *)
  evtF asegs RNG (free_fast_post DI L ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n nb fst0 lst qb b1 actx lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x338f4) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 0).
Variable ek : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 1).
Variable g : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 2).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 3).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 4).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 5).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 6).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 7).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 8).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 9).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 10).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 11).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 12).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 13).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 14).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 15).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 16).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 17).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 18).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 19).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 20).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 21).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 22).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 23).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 24).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 25).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 26).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 27).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 28).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 29).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 30).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 31).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 32).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 33).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 34).
Variable F : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 35).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 36).
Variable m : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 37).
Variable t : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 38).
Variable ctx : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 39).
Variable hm : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 40).
Variable n : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 41).
Variable b1 : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 42).
Variable actx : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 43).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 44).
Variable nb : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 45).
Variable fst0 : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 46).
Variable lst : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 47).
Variable qb : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 48).
Variable S : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 49).
Variable sz : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 50).
Variable pc : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 51).
Variable uw : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 52).
Variable top : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 53).
Variable bot : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 54).
Variable sj : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 55).
Variable tb : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 56).
Variable sjunk : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 57).
Variable trt : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 58).
#[using="Type"] Lemma dfn_fast_spec__body : ltac:(let T := type of (fun (h : dfn_fast_spec__stmt) => h L ek g RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m t ctx hm n b1 actx lo nb fst0 lst qb S sz pc uw top bot sj tb sjunk trt) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (ek, (g, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (t, (ctx, (hm, (n, (b1, (actx, (lo, (nb, (fst0, (lst, (qb, (S, (sz, (pc, (uw, (top, (bot, (sj, (tb, (sjunk, trt))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) as _.

  intros ST CEIL LO MI TP Ha0 Ha1 Ha2 Ha3 Ha4 Ha5 AC PC MCS CF34 GPG PGC HK QK GF FLG FL IAS IAM CT8 TT0 UW STATS LSJ QC NB QB QBN FST LST
         CX0 C0 C1 T0 T1 TAL CT2 HD HUW B1 B13 N AL HLO TCH HHI HCE SH DHT DHC EK ES DK DS DEP N0 N1 R0 R1 DHN DHS DTN DTS DCN DCS XTNO XTST
         SS TB LTB SZE SZB TRF TRU SGE S47 RS RIMG RTLS RSTK RCTX RT RNO RST RH RSH CI NI SI TI.
  band_int TI. (pose proof (ablk_lin _ _ HLO) as ndP__; nd_pre ndP__ 4%nat; intros HL1 HL2 HL3 HL4; nd_post). unfold AIMG_HI in HL1. band_int HLO. band_lin. band_int C0. band_int T0. band_int N0. band_int R0.   (* [comment removed for export] *)
  pose proof PC as PC'. destruct PC' as (GOT6 & _).
  assert (RUP : n <= rup n 8 <= n + 7 /\ rup n 8 mod 8 = 0) by (clear -N; unfold rup; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
  assert (SHB : 2148238848 <= shad (hm + 16) /\ shad (hm + 16) + shlen (rup n 8) <= 0x10007fff8000 /\ 0 < shlen (rup n 8)).
  { clear -N HLO HL1 HHI HCE. atop_facts. unfold shad, shlen, ASHOFF, rup in *. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold Q_MAX in *. Z.div_mod_to_equations. lia. }
  (pose proof (ek_pre_pure ek RNG L t nb lst n hm m EK ES TI ltac:(unfold AIMG_HI; lia) NI SI) as ndP__; nd_pre ndP__ 14%nat; intros PF1 PF2 PF3 PF4 PF5 PF6 PF7 PF8 PL0 PL1 PB0 PB1 PL2 PB2; nd_post).
  (pose proof (dk_pre_pure ek g RNG L t lst hm (qb + ek_delta ek n) m DK DS TI ltac:(unfold AIMG_HI; lia) NI SI PF1 PF3 PF5 PF6 PL0 PL1 PL2) as ndP__; nd_pre ndP__ 7%nat; intros DF1 DF2 DF3 DF4 DG0 DG1 DG2; nd_post).
  (pose proof (qsz_int lst PL0 ltac:(clear -PL1; atop_facts; lia)) as ndP__; nd_pre ndP__ 5%nat; intros zq QZ0 QZ1 QZ2 QZ3; nd_post).   (* [comment removed for export] *)
  unfold AIMG_HI in *.
  word_range sp SPR.
  box DHT. box DHC. box DHN. box DHS. box DTN. box DTS. box DCN. box DCS. box CT2.
  box PF1. box PF2. box PF3. box PF4. box PF5. box PF6. box PF7. box PF8. box DF1. box DF2. box DF3. box DF4. box PL2. box DG2.
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (dfn_front_spec DI L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
              t ctx hm n b1 actx lo S sz pc uw top bot sj tb trt).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact ST | exact IAS]
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => exact AC
         | |- ADEPOT _ _ _ => exact DEP
         | |- In _ _ => exact TRU
         | |- u64arr _ _ (_ + 2800) _ => exact STATS
         | |- u64arr _ _ _ _ => exact TB
         | |- map _ _ = _ => exact TRF
         | |- forall j, _ => exact IAM
         | |- _ \/ _ => first [unboxed DHT | unboxed DHC | unboxed DHN | unboxed DHS | unboxed DTN | unboxed DTS | unboxed DCN | unboxed DCS | unboxed CT2]
         | |- rng _ _ _ => first [exact RS | solve_rng]
         | |- @eq word _ _ => first [exact TP | exact Ha0 | exact Ha1 | exact Ha2 | exact Ha3 | exact Ha4 | exact Ha5]
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _] => exact TT0
         | |- rw_cells _ _ _ [C8 _; C4 _; C4 _] => exact SS
         | |- rw_cells _ _ (_ + 16) _ => exact HUW
         | |- rw_cells _ _ (_ + 8) _ => exact CT8
         | |- rw_cells _ _ (_ + 3168) _ => exact UW
         end.
    all: try eassumption. all: try (unfold AIMG_HI, Q_MAX in *; lia).
    all: match goal with |- ?G => idtac "REMF" G end. }
  cbv beta. intros ms1 PFR. unfold dfn_front_post in PFR.
  (nd_pre PFR 13%nat; intros id t0a t1a t2a a6a a7a t3a t4a t5a t6a m1 sj1 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 14%nat; intros MUf WMf MIf STf IDR HD1 FC1 STATS1 LSJ1 UW1 FL1 IAS1 IAM1 DEP1; nd_post).
  (* [comment removed for export] *)
  xport QK MUf WMf ltac:(lia). xport GF MUf WMf ltac:(lia). xport FLG MUf WMf ltac:(lia).
  xport QC MUf WMf ltac:(ub DHT; ub DTN; ub DTS; ylia).
  xport SH MUf WMf ltac:(band_disj).   (* [comment removed for export] *)
  assert (PC1 : poison_cells m1).
  { eapply poison_cells_frame2; [exact PC | exact MUf | exact WMf |].
    repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
  assert (EK1 : ek_pre ek RNG t nb lst n hm m1).
  { eapply (ek_pre_front L sp t hm lo m m1); [exact MUf | exact WMf | ..]; try (unfold AIMG_HI; lia).
    all: first [exact TI | unboxed DHT | unboxed DTN | unboxed DTS | exact EK | exact ES]. }
  assert (DK1 : dk_pre ek g RNG t lst hm (qb + ek_delta ek n) m1).
  { eapply (dk_pre_front L sp t hm lo m m1); [exact MUf | exact WMf | ..]; try (unfold AIMG_HI; lia).
    all: first [exact TI | unboxed DHT | unboxed DTN | unboxed DTS | exact DK | exact DS]. }
  clear EK DK PC.
  (* [comment removed for export] *)
  eapply evtF_mono.
  { eapply (put_tail_spec ek g t hm lst RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 n nb fst0 qb b1 actx lo sjunk).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact STf
         | |- mem_inv _ _ => exact MIf
         | |- poison_cells _ => exact PC1
         | |- ek_pre _ _ _ _ _ _ _ _ => exact EK1
         | |- dk_pre _ _ _ _ _ _ _ _ => exact DK1
         | |- @eq word _ _ => reflexivity
         | |- _ \/ _ => ub DHT; ylia
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD1
         | |- rw_cells _ _ (shad _) _ => exact SH
         | |- rw_cells _ _ (_ + 80) _ => exact QC
         | |- iclr _ _ => exact TI
         end.
    all: try eassumption. all: try (unfold AIMG_HI, Q_MAX in *; lia).
    all: match goal with |- ?G => idtac "REMP" G end. }
  cbv beta. intros ms2 PP. unfold put_tail_post in PP.
  (nd_pre PP 17%nat; intros t0b t1b t2b a0b a1b a2b a3b a4b a5b a6b a7b t3b t4b t5b t6b m2 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 9%nat; intros MUp WMp MIp STp SH2 HD2 QC2 EKP DKP; nd_post).
  (* [comment removed for export] *)
  xport FC1 MUp WMp ltac:(ub DHT; ub PF1; ub PF2; ub DF1; ylia).
  xport STATS1 MUp WMp ltac:(rewrite LSJ1; ub PF3; ub PF4; ub DF2; ylia).
  xport UW1 MUp WMp ltac:(ub PF3; ub PF4; ub DF2; ylia).
  xport FL1 MUp WMp ltac:(ub PL2; ub DG2; ylia). xport IAS1 MUp WMp ltac:(ub PL2; ub DG2; ylia).
  assert (IAM2 : forall j, 0 <= j < 32768 -> bytes_at asegs m2 (0xaf808 + 8 * j) (le8 (Z_to_bv 64 0))).
  { (intros j Hj; eapply bytes_at_agree; [exact (IAM1 j Hj)|];
    intros i Hi; apply MUp; cbn [outside]; rewrite length_le8 in Hi; rewrite wa_unsigned by lia; ub PL2; ub DG2; ylia). }
  clear IAM1.
  assert (DEP2 : ADEPOT DI L m2).
  { eapply (adi_frame DI); [exact DEP1 | exact MUp | exact WMp |].
    ((first [ apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [ lia |lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] | first [ apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [ lia |lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] | first [ apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [ ub DTN; ub DTS; ylia |lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] | first [ apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [ ub DTN; ub DTS; ylia |lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] | first [ apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [ ub DTN; ub DTS; ylia |lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] | first [ apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [ ub PF5; ub PF6; ub PL2; ylia |lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] | first [ apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [ ub PF7; ub PF8; ylia |lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] | first [ apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [ lia |lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] | first [ apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [ lia |lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] | first [ apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [ ub DF3; ub DF4; ub DG2; ylia |lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] |])] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] |]) ]); apply Forall_nil). }
  clear DEP1.
  pose proof STp as ST3.
  (* [comment removed for export] *)
  assert (MU : munch (free_W L sp t hm n lst ek g) m m2).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUp]].
    eapply munch_weaken; [| exact MUf].
    all: solve_sub_fp sp. }
  assert (WM : wmono asegs m m2) by (eapply wmono_trans; [exact WMf| exact WMp]).
  unfold free_fast_post. exists id. do 15 eexists. exists m2, sj1.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MIp|]. split; [exact ST3|]. split; [exact IDR|].
  split; [exact HD2|]. split; [exact FC1|]. split; [exact SH2|]. split; [exact QC2|]. split; [exact EKP|]. split; [exact DKP|].
  split; [exact STATS1|]. split; [exact LSJ1|]. split; [exact UW1|]. split; [exact FL1|]. split; [exact IAS1|]. split; [exact IAM2|].
  exact DEP2.
Qed.
End Zd1.
#[using="Type"] Lemma dfn_fast_spec : ltac:(let t := eval cbv delta [dfn_fast_spec__stmt] in dfn_fast_spec__stmt in exact t).
Proof. exact dfn_fast_spec__body. Qed.
End WithDepot.
End CANSEC2.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_afree_iseg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_front.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tail.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_icpt.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_adeallocfn_front.TwB.
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
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.
(* [comment removed for export] *)
Local Ltac qlia := first [ LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                         | LiaTuning.zify_prune; Zify.zify; xlia zchecker ].
Local Ltac leaf2 := first [ left; qlia | right; qlia | qlia ].
Local Ltac band_leaf :=
  first [ leaf2
        | match goal with B : sclr ?a _ |- context [?a] =>
            let B' := fresh "BB" in pose proof B as B'; unfold sclr, KLS in B'; destruct B' as [B'|B']; leaf2 end
        | match goal with B : iclr ?a _ |- context [?a] =>
            let B' := fresh "BB" in pose proof B as B'; unfold iclr, AIMG_LO, AIMG_HI in B'; destruct B' as [_ [B'|B']]; leaf2 end
        | match goal with B : ablk ?a _ |- context [?a] =>
            let B' := fresh "BB" in pose proof B as B'; unfold ablk, KLS, AIMG_HI in B'; destruct B' as [[? B']|[B' ?]]; leaf2 end
        | lia ].
Local Ltac band_disj := cbn [disjoint_from fst snd]; repeat match goal with |- _ /\ _ => split end; first [exact I | band_leaf].
(* [comment removed for export] *)
Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6307840 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6307840 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (sclr_int a n H G1 G2) 4%nat; intros k A B C; nd_post); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (iclr_int a n H G2) 5%nat; intros k A B C D; nd_post); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>      (* [comment removed for export] *)
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (iclr_int a n H G2) 5%nat; intros k A B C D; nd_post); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.


Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC2. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithDepot.
Variable DI : ADepotIface.

Notation free_W L sp t hm n lst ek g :=
  ([(bv_unsigned sp - 4096, bv_unsigned sp); (0xafc00, 0xafc00 + 0x81030); (0x13e488, 0x13e488 + 4);
    (t + 3168, t + 3169); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608);
    (shad (hm + 16), shad (hm + 16) + shlen (rup n 8)); (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792);
    (lst, lst + qsz lst); (ek_b ek lst, ek_b ek lst + 8192);
    (0xab708, 0xab708 + 4); (0xab710, 0xab710 + 32); (dk_glst g lst, dk_glst g lst + 8)]%Z) (only parsing).

Definition dfn_fast_spec__stmt : Prop := forall (L : alayout) (ek : enq_kind) (g : gqd) RNG
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem)
    (t ctx hm n b1 actx lo nb fst0 lst qb S sz pc : Z) (uw top bot : word) (sj tb : list word) (sjunk : list byte) (trt : list Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 (hm + 16) -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 0 -> a4 = Z_to_bv 64 S -> a5 = Z_to_bv 64 1 ->
  (* [comment removed for export] *)
  allocA_cells m ctx t -> poison_cells m ->
  rw_cells asegs m 0xaf6fc [C4 (Z_to_bv 64 30)] ->
  rw_cells asegs m 0x14054a [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m 0xa5870 [C8 (Z_to_bv 64 0x13e4a0)] -> rw_cells asegs m 0x13e4a0 [C8 (Z_to_bv 64 4096)] ->
  rw_cells asegs m 0x1404c8 [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m 0xab6b0 [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->
  rw_cells asegs m 0xa5888 [C8 (Z_to_bv 64 AFLAGS)] ->
  rw_cells asegs m 0xac224 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->
  (* [comment removed for export] *)
  rw_cells asegs m 0x13e488 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  stk asegs m 0xafc00 (0xafc00 + 0x81030) ->
  (forall j, 0 <= j < 32768 -> bytes_at asegs m (0xafc08 + 8 * j) (le8 (Z_to_bv 64 0))) ->
  (* [comment removed for export] *)
  rw_cells asegs m (ctx + 8) [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m t [C8 (Z_to_bv 64 ctx); C8 top; C8 bot] ->
  rw_cells asegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  rw_cells asegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= qb -> qb + n + 8192 < 2^62 -> 0 <= fst0 < 2^64 -> 0 <= lst < 2^64 ->
  0 < ctx -> sclr ctx 65536 -> ctx + 4096 <= ATOP ->
  sclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> t mod 4096 = 0 -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  (* [comment removed for export] *)
  rw_cells asegs m hm [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  rw_cells asegs m (hm + 16) [C8 uw] -> 0 <= b1 < 256 -> Z.land b1 3 = 1 -> 1 <= n <= Q_MAX -> hm mod 16 = 0 ->
  ablk hm (hm + 16 + rup n 8) -> tclr hm 24 -> hm + 16 + rup n 8 <= ATOP -> hm + 24 <= ATOP ->
  rw_cells asegs m (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) sjunk] ->
  (hm + 24 <= t \/ t + 4096 <= hm) -> (hm + 24 <= ctx \/ ctx + 4096 <= hm) ->
  (* [comment removed for export] *)
  ek_pre ek RNG t nb lst n hm m -> ek_seps ek L hm lst ->
  dk_pre ek g RNG t lst hm (qb + ek_delta ek n) m -> dk_seps g L hm ->
  (* [comment removed for export] *)
  ADEPOT DI L m ->
  sclr (al_nodes L) 1048576 -> al_nodes L + 1048576 <= ATOP -> sclr (al_store L) 8388608 -> al_store L + 8388608 <= ATOP ->
  (hm + 24 <= al_nodes L \/ al_nodes L + 1048576 <= hm) -> (hm + 24 <= al_store L \/ al_store L + 8388608 <= hm) ->
  (t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) -> (t + 4096 <= al_store L \/ al_store L + 8388608 <= t) ->
  (ctx + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= ctx) -> (ctx + 4096 <= al_store L \/ al_store L + 8388608 <= ctx) -> tclr (al_nodes L) 1048576 -> tclr (al_store L) 8388608 ->
  (* [comment removed for export] *)
  rw_cells asegs m S [C8 (Z_to_bv 64 (S + 16)); C4 (Z_to_bv 64 sz); C4 (Z_to_bv 64 0)] ->
  u64arr asegs m (S + 16) tb -> length tb = 255%nat ->
  sz = 1 + Z.of_nat (length trt) -> sz <= 255 ->
  map bv_unsigned (firstn (Datatypes.S (length trt)) tb) = pc :: trt -> In (pc :: trt) (al_U L) ->
  bv_unsigned sp <= S -> S + 2056 <= 2^47 -> rng RNG S 2056 ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 -> rng RNG hm 24 -> rng RNG (shad (hm + 16)) (shlen (rup n 8)) ->
  AIMG_HI <= ctx -> AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L -> iclr t 4096 ->      (* [comment removed for export] *)
  evtF asegs RNG (free_fast_post DI L ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n nb fst0 lst qb b1 actx lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3395c) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 0).
Variable ek : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 1).
Variable g : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 2).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 3).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 4).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 5).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 6).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 7).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 8).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 9).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 10).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 11).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 12).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 13).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 14).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 15).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 16).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 17).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 18).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 19).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 20).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 21).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 22).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 23).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 24).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 25).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 26).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 27).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 28).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 29).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 30).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 31).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 32).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 33).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 34).
Variable F : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 35).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 36).
Variable m : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 37).
Variable t : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 38).
Variable ctx : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 39).
Variable hm : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 40).
Variable n : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 41).
Variable b1 : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 42).
Variable actx : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 43).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 44).
Variable nb : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 45).
Variable fst0 : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 46).
Variable lst : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 47).
Variable qb : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 48).
Variable S : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 49).
Variable sz : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 50).
Variable pc : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 51).
Variable uw : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 52).
Variable top : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 53).
Variable bot : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 54).
Variable sj : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 55).
Variable tb : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 56).
Variable sjunk : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 57).
Variable trt : ltac2:(SecDietF.SzSecF.ty 'dfn_fast_spec__stmt 58).
#[using="Type"] Lemma dfn_fast_spec__body : ltac:(let T := type of (fun (h : dfn_fast_spec__stmt) => h L ek g RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m t ctx hm n b1 actx lo nb fst0 lst qb S sz pc uw top bot sj tb sjunk trt) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (ek, (g, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (t, (ctx, (hm, (n, (b1, (actx, (lo, (nb, (fst0, (lst, (qb, (S, (sz, (pc, (uw, (top, (bot, (sj, (tb, (sjunk, trt))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) as _.

  intros ST CEIL LO MI TP Ha0 Ha1 Ha2 Ha3 Ha4 Ha5 AC PC MCS CF34 GPG PGC HK QK GF FLG FL IAS IAM CT8 TT0 UW STATS LSJ QC NB QB QBN FST LST
         CX0 C0 C1 T0 T1 TAL CT2 HD HUW B1 B13 N AL HLO TCH HHI HCE SH DHT DHC EK ES DK DS DEP N0 N1 R0 R1 DHN DHS DTN DTS DCN DCS XTNO XTST
         SS TB LTB SZE SZB TRF TRU SGE S47 RS RIMG RTLS RSTK RCTX RT RNO RST RH RSH CI NI SI TI.
  band_int TI. (pose proof (ablk_lin _ _ HLO) as ndP__; nd_pre ndP__ 4%nat; intros HL1 HL2 HL3 HL4; nd_post). unfold AIMG_HI in HL1. band_int HLO. band_lin. band_int C0. band_int T0. band_int N0. band_int R0.   (* [comment removed for export] *)
  pose proof PC as PC'. destruct PC' as (GOT6 & _).
  assert (RUP : n <= rup n 8 <= n + 7 /\ rup n 8 mod 8 = 0) by (clear -N; unfold rup; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
  assert (SHB : 2148239360 <= shad (hm + 16) /\ shad (hm + 16) + shlen (rup n 8) <= 0x10007fff8000 /\ 0 < shlen (rup n 8)).
  { clear -N HLO HL1 HHI HCE. atop_facts. unfold shad, shlen, ASHOFF, rup in *. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold Q_MAX in *. Z.div_mod_to_equations. lia. }
  (pose proof (ek_pre_pure ek RNG L t nb lst n hm m EK ES TI ltac:(unfold AIMG_HI; lia) NI SI) as ndP__; nd_pre ndP__ 14%nat; intros PF1 PF2 PF3 PF4 PF5 PF6 PF7 PF8 PL0 PL1 PB0 PB1 PL2 PB2; nd_post).
  (pose proof (dk_pre_pure ek g RNG L t lst hm (qb + ek_delta ek n) m DK DS TI ltac:(unfold AIMG_HI; lia) NI SI PF1 PF3 PF5 PF6 PL0 PL1 PL2) as ndP__; nd_pre ndP__ 7%nat; intros DF1 DF2 DF3 DF4 DG0 DG1 DG2; nd_post).
  (pose proof (qsz_int lst PL0 ltac:(clear -PL1; atop_facts; lia)) as ndP__; nd_pre ndP__ 5%nat; intros zq QZ0 QZ1 QZ2 QZ3; nd_post).   (* [comment removed for export] *)
  unfold AIMG_HI in *.
  word_range sp SPR.
  box DHT. box DHC. box DHN. box DHS. box DTN. box DTS. box DCN. box DCS. box CT2.
  box PF1. box PF2. box PF3. box PF4. box PF5. box PF6. box PF7. box PF8. box DF1. box DF2. box DF3. box DF4. box PL2. box DG2.
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (dfn_front_spec DI L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
              t ctx hm n b1 actx lo S sz pc uw top bot sj tb trt).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact ST | exact IAS]
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => exact AC
         | |- ADEPOT _ _ _ => exact DEP
         | |- In _ _ => exact TRU
         | |- u64arr _ _ (_ + 2800) _ => exact STATS
         | |- u64arr _ _ _ _ => exact TB
         | |- map _ _ = _ => exact TRF
         | |- forall j, _ => exact IAM
         | |- _ \/ _ => first [unboxed DHT | unboxed DHC | unboxed DHN | unboxed DHS | unboxed DTN | unboxed DTS | unboxed DCN | unboxed DCS | unboxed CT2]
         | |- rng _ _ _ => first [exact RS | solve_rng]
         | |- @eq word _ _ => first [exact TP | exact Ha0 | exact Ha1 | exact Ha2 | exact Ha3 | exact Ha4 | exact Ha5]
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _] => exact TT0
         | |- rw_cells _ _ _ [C8 _; C4 _; C4 _] => exact SS
         | |- rw_cells _ _ (_ + 16) _ => exact HUW
         | |- rw_cells _ _ (_ + 8) _ => exact CT8
         | |- rw_cells _ _ (_ + 3168) _ => exact UW
         end.
    all: try eassumption. all: try (unfold AIMG_HI, Q_MAX in *; lia).
    all: match goal with |- ?G => idtac "REMF" G end. }
  cbv beta. intros ms1 PFR. unfold dfn_front_post in PFR.
  (nd_pre PFR 13%nat; intros id t0a t1a t2a a6a a7a t3a t4a t5a t6a m1 sj1 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 14%nat; intros MUf WMf MIf STf IDR HD1 FC1 STATS1 LSJ1 UW1 FL1 IAS1 IAM1 DEP1; nd_post).
  (* [comment removed for export] *)
  xport QK MUf WMf ltac:(lia). xport GF MUf WMf ltac:(lia). xport FLG MUf WMf ltac:(lia).
  xport QC MUf WMf ltac:(ub DHT; ub DTN; ub DTS; ylia).
  xport SH MUf WMf ltac:(band_disj).   (* [comment removed for export] *)
  assert (PC1 : poison_cells m1).
  { eapply poison_cells_frame2; [exact PC | exact MUf | exact WMf |].
    repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
  assert (EK1 : ek_pre ek RNG t nb lst n hm m1).
  { eapply (ek_pre_front L sp t hm lo m m1); [exact MUf | exact WMf | ..]; try (unfold AIMG_HI; lia).
    all: first [exact TI | unboxed DHT | unboxed DTN | unboxed DTS | exact EK | exact ES]. }
  assert (DK1 : dk_pre ek g RNG t lst hm (qb + ek_delta ek n) m1).
  { eapply (dk_pre_front L sp t hm lo m m1); [exact MUf | exact WMf | ..]; try (unfold AIMG_HI; lia).
    all: first [exact TI | unboxed DHT | unboxed DTN | unboxed DTS | exact DK | exact DS]. }
  clear EK DK PC.
  (* [comment removed for export] *)
  eapply evtF_mono.
  { eapply (put_tail_spec ek g t hm lst RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 n nb fst0 qb b1 actx lo sjunk).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact STf
         | |- mem_inv _ _ => exact MIf
         | |- poison_cells _ => exact PC1
         | |- ek_pre _ _ _ _ _ _ _ _ => exact EK1
         | |- dk_pre _ _ _ _ _ _ _ _ => exact DK1
         | |- @eq word _ _ => reflexivity
         | |- _ \/ _ => ub DHT; ylia
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD1
         | |- rw_cells _ _ (shad _) _ => exact SH
         | |- rw_cells _ _ (_ + 80) _ => exact QC
         | |- iclr _ _ => exact TI
         end.
    all: try eassumption. all: try (unfold AIMG_HI, Q_MAX in *; lia).
    all: match goal with |- ?G => idtac "REMP" G end. }
  cbv beta. intros ms2 PP. unfold put_tail_post in PP.
  (nd_pre PP 17%nat; intros t0b t1b t2b a0b a1b a2b a3b a4b a5b a6b a7b t3b t4b t5b t6b m2 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 9%nat; intros MUp WMp MIp STp SH2 HD2 QC2 EKP DKP; nd_post).
  (* [comment removed for export] *)
  xport FC1 MUp WMp ltac:(ub DHT; ub PF1; ub PF2; ub DF1; ylia).
  xport STATS1 MUp WMp ltac:(rewrite LSJ1; ub PF3; ub PF4; ub DF2; ylia).
  xport UW1 MUp WMp ltac:(ub PF3; ub PF4; ub DF2; ylia).
  xport FL1 MUp WMp ltac:(ub PL2; ub DG2; ylia). xport IAS1 MUp WMp ltac:(ub PL2; ub DG2; ylia).
  assert (IAM2 : forall j, 0 <= j < 32768 -> bytes_at asegs m2 (0xafc08 + 8 * j) (le8 (Z_to_bv 64 0))).
  { (intros j Hj; eapply bytes_at_agree; [exact (IAM1 j Hj)|];
    intros i Hi; apply MUp; cbn [outside]; rewrite length_le8 in Hi; rewrite wa_unsigned by lia; ub PL2; ub DG2; ylia). }
  clear IAM1.
  assert (DEP2 : ADEPOT DI L m2).
  { eapply (adi_frame DI); [exact DEP1 | exact MUp | exact WMp |].
    ((first [ apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [ lia |lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] | first [ apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [ lia |lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] | first [ apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [ ub DTN; ub DTS; ylia |lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] | first [ apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [ ub DTN; ub DTS; ylia |lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] | first [ apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [ ub DTN; ub DTS; ylia |lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] | first [ apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [ ub PF5; ub PF6; ub PL2; ylia |lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] | first [ apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [ ub PF7; ub PF8; ylia |lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] | first [ apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [ lia |lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] | first [ apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [ lia |lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] | first [ apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [ ub DF3; ub DF4; ub DG2; ylia |lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] |])] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub PF5; ub PF6; ub PL2; ylia | ub PF7; ub PF8; ylia | ub DF3; ub DF4; ub DG2; ylia] |]) ]); apply Forall_nil). }
  clear DEP1.
  pose proof STp as ST3.
  (* [comment removed for export] *)
  assert (MU : munch (free_W L sp t hm n lst ek g) m m2).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUp]].
    eapply munch_weaken; [| exact MUf].
    all: solve_sub_fp sp. }
  assert (WM : wmono asegs m m2) by (eapply wmono_trans; [exact WMf| exact WMp]).
  unfold free_fast_post. exists id. do 15 eexists. exists m2, sj1.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MIp|]. split; [exact ST3|]. split; [exact IDR|].
  split; [exact HD2|]. split; [exact FC1|]. split; [exact SH2|]. split; [exact QC2|]. split; [exact EKP|]. split; [exact DKP|].
  split; [exact STATS1|]. split; [exact LSJ1|]. split; [exact UW1|]. split; [exact FL1|]. split; [exact IAS1|]. split; [exact IAM2|].
  exact DEP2.
Qed.
End Zd1.
#[using="Type"] Lemma dfn_fast_spec : ltac:(let t := eval cbv delta [dfn_fast_spec__stmt] in dfn_fast_spec__stmt in exact t).
Proof. exact dfn_fast_spec__body. Qed.
End WithDepot.
End CANSEC2.
End TwB.
End F_adeallocfn_icpt.

(* [comment removed for export] *)
Module F_afree_null.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecSlog__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3 F_aunwind. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc1b__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_s__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_adrain__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aunwind OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc1b__A3W.F_aunwind2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_afree_s OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_aintal OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_afree_iseg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_front OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_icpt.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
#[using="Type"] Lemma rw_cells_of_u64arr' : forall m A ws,
  u64arr asegs m A ws -> rw_cells asegs m A [CB (8 * length ws) (u64s ws)].
Proof. exact rw_cells_of_u64arr. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma dealloc_null_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x338cc) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST CEIL LO MI -> RSTK. atop_facts.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  word_range sp SPR.
  do 9 step.                                   (* [comment removed for export] *)
  step.                                        (* [comment removed for export] *)
  carve_frame 64%nat ST.
  do 9 step.                                   (* [comment removed for export] *)
  step. if_lit.                                (* [comment removed for export] *)
  do 8 step.                                   (* [comment removed for export] *)
  zstep. step.                                 (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  finish.
Qed.

(* [comment removed for export] *)
Definition free_null_post (sp : word) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 4096, bv_unsigned sp); (0xaf800, 0xaf800 + 0x81030); (0x13e088, 0x13e088 + 4); (t + 3168, t + 3169)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (t + 3168) [C1 (Z_to_bv 8 0)]
    /\ rw_cells asegs m' 0x13e088 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ stk asegs m' 0xaf800 (0xaf800 + 0x81030)
    /\ (forall j, 0 <= j < 32768 -> bytes_at asegs m' (0xaf808 + 8 * j) (le8 (Z_to_bv 64 0))).

Definition free_null_spec__stmt : Prop := forall (ia : bool) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem)
    (t ctx lo top bot : Z) (trt : list Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 0 ->
  bv_unsigned sp mod 16 = 0 ->
  (* [comment removed for export] *)
  allocA_cells m ctx t ->
  rw_cells asegs m 0xa54a0 [C8 (Z_to_bv 64 0x140128); C8 (Z_to_bv 64 0xabdf8); C8 (Z_to_bv 64 0xae5f8);
                             C8 (Z_to_bv 64 0xaf2e8); C8 (Z_to_bv 64 0xaf2f0); C8 (Z_to_bv 64 0xaf2e0)] ->
  rw_cells asegs m 0xaf2fc [C4 (Z_to_bv 64 30)] ->
  rw_cells asegs m 0x14014a [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m 0xa5490 [C8 (Z_to_bv 64 0x13e0a0)] -> rw_cells asegs m 0x13e0a0 [C8 (Z_to_bv 64 4096)] ->
  (* [comment removed for export] *)
  rw_cells asegs m 0x13e088 [C1 (Z_to_bv 8 (if ia then 1 else 0)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  stk asegs m 0xaf800 (0xaf800 + 0x81030) ->
  (ia = true -> forall j, 0 <= j < 32768 -> bytes_at asegs m (0xaf808 + 8 * j) (le8 (Z_to_bv 64 0))) ->
  (* [comment removed for export] *)
  rw_cells asegs m (ctx + 8) [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m t [C8 (Z_to_bv 64 ctx); C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)] ->
  rw_cells asegs m (t + 40) [C1 (Z_to_bv 8 0)] -> rw_cells asegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  0 < ctx -> AIMG_HI <= ctx -> ctx + 4096 <= ATOP ->
  iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  (* [comment removed for export] *)
  afree_unw RNG lo m top sp s0 ra trt ->
  bv_unsigned s0 <> bv_unsigned sp + 8 ->
  0 <= bot -> bot < bv_unsigned sp -> bot < top -> 4096 <= top <= 2^47 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  evtF asegs RNG (free_null_post sp ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable ia : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 5).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 6).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 7).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 8).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 9).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 10).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 11).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 12).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 13).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 14).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 15).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 16).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 17).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 18).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 19).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 20).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 21).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 22).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 23).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 24).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 25).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 26).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 27).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 28).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 29).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 30).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 31).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 32).
Variable F : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 33).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 34).
Variable m : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 35).
Variable t : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 36).
Variable ctx : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 37).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 38).
Variable top : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 39).
Variable bot : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 40).
Variable trt : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 41).
#[using="Type"] Lemma free_null_spec__body : ltac:(let T := type of (fun (h : free_null_spec__stmt) => h ia RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m t ctx lo top bot trt) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (ia, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (t, (ctx, (lo, (top, (bot, trt)))))))))))))))))))))))))))))))))))))))))) as _.

  intros ST CEIL LO MI TP Ha0 SP16 AC GOT6 MCS CF34 GPG PGC FL IAS IAM CT8 TT0 SW UW CX0 C0 C1 T0 T1 CT2
         UNW S0NE B0 BB BOTOP TOP RA4 RANE RIMG RTLS RSTK RCTX RT. band_lin.   (* [comment removed for export] *)
  pose proof (afree_unw_length _ _ _ _ _ _ _ _ UNW) as LTRT.
  pose proof (afree_unw_sp47 _ _ _ _ _ _ _ _ UNW ltac:(clear -TOP; lia)) as SP47.
  pose proof AC as AC'. (nd_pre AC' 8%nat; intros INI RSS IMAX TI TK T88 TSD CT; nd_post).
  unfold AIMG_HI, AINSTANCE, ATP88, ATSD, ATSDI, ATSDK, AINITED, ARSSLIM, GOT_PGSZ, APGSZ, AFREE_SYM, AFREE_PC in *.
  word_range sp SPR. word_range s0 S0R. word_range ra RAR.
  box CT2.
  pose proof TT0 as TTx. rw_split TTx 1%nat TTc TT. clear TTc.
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (ficptA_spec 0 ia RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo);
      try eassumption; try (unfold AIA_FLAG, AIA_BASE, AIA_SIZE, AIA_MAP1; lia).
    all: try lazymatch goal with
         | |- rw_cells _ _ AIA_FLAG _ => exact FL
         | |- stk _ _ AIA_BASE _ => exact IAS
         | |- _ = true -> _ => exact IAM
         | |- rng _ _ _ => solve_rng
         end.
    all: match goal with |- ?G => idtac "REMA" G end. }
  cbv beta. intros ms1 PA. unfold ficptA_post in PA.
  (nd_pre PA 13%nat; intros t0a t1a t2a a6a a7a t3a t4a t5a t6a m1 junk1 junk2 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 10%nat; intros MUa WMa MIa STa FRA FRt FRs FL1 IAS1 IAM1; nd_post).
  (* [comment removed for export] *)
  pose proof FRs as FRs0. rw_split FRs0 7%nat FRsx FRsr. clear FRsx.
  destruct FRsr as [[_ BSR] _]. cbn [cells_bytes cbytes app] in BSR. rewrite app_nil_r in BSR.
  apply bytes_at_app in BSR. destruct BSR as [BS0 BRA]. rewrite length_le8 in BRA.
  replace (bv_unsigned sp + -16 + Z.of_nat 8) with (bv_unsigned sp - 8) in BRA by lia.
  replace (bv_unsigned sp + -16) with (bv_unsigned sp - 16) in BS0 by lia.
  assert (UC1 : forall tr, trt = bv_unsigned ra :: tr -> uchain m top 352956 (bv_unsigned sp) (bv_unsigned s0) 28%nat tr -> bv_unsigned sp + 16 < top ->
                uchain m1 top 352956 bot (bv_unsigned sp) 29%nat ([bv_unsigned ra] ++ tr)).
  { intros tr _ UC BTX. replace ([bv_unsigned ra] ++ tr) with ((if bv_unsigned ra =? 352956 then [] else [bv_unsigned ra]) ++ tr)
      by (replace (bv_unsigned ra =? 352956) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
    eapply (uc_step m1 top 352956 bot (bv_unsigned sp) 29%nat (bv_unsigned s0) (bv_unsigned ra) tr); try lia.
    - rewrite Z_to_bv_bv_unsigned. exact BS0.
    - rewrite Z_to_bv_bv_unsigned. exact BRA.
    - replace (bv_unsigned ra =? 352956) with false by (symmetry; apply Z.eqb_neq; lia). cbn [Nat.pred].
      destruct (Z_le_gt_dec (bv_unsigned sp + 16) (bv_unsigned s0)) as [GE|LT].
      + eapply uchain_frame; [exact UC|]. intros a Ha. apply MUa. cbn [outside]. rewrite unsigned_lit by lia. lia.
      + inversion UC; subst; [apply uc_stop; assumption | exfalso | exfalso]; Z.div_mod_to_equations; lia. }
  clear BS0 BRA.
  (* [comment removed for export] *)
  xport TI MUa WMa ltac:(lia). xport TK MUa WMa ltac:(lia). xport T88 MUa WMa ltac:(lia). xport TSD MUa WMa ltac:(lia).
  xport CT MUa WMa ltac:(lia). xport GPG MUa WMa ltac:(lia). xport PGC MUa WMa ltac:(lia). xport TT MUa WMa ltac:(lia).
  xport TT0 MUa WMa ltac:(lia). xport CT8 MUa WMa ltac:(lia).
  xport SW MUa WMa ltac:(lia). xport UW MUa WMa ltac:(lia). xport INI MUa WMa ltac:(lia).
  pose proof FRA as FRA0. rw_split FRA0 1%nat FRp FRz. rw_split FRz 1%nat SZC TAG.
  change 2040%nat with (8 * 255)%nat in FRt. destruct (u64arr_of_CB _ _ 255%nat _ FRt) as [TB LTB].
  pose proof FRs as FRs1. rw_split FRs1 1%nat BPJ REST.
  replace (bv_unsigned sp + -2120) with (bv_unsigned sp + -2128 + 8) in SZC by lia.
  replace (bv_unsigned sp + -2112) with (bv_unsigned sp + -2128 + 16) in TB by lia.
  replace (bv_unsigned sp + -72) with (bv_unsigned sp + -2128 + 2056) in BPJ by lia.
  (* [comment removed for export] *)
  step.                                                          (* [comment removed for export] *)
  name_sp sp (-2128).
  eapply evtF_cut with (P := unwind_impl_post (bv_unsigned sp + -2128) 352956 (bv_unsigned sp) t _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc lo trt m1).
  { destruct UNW as [(tr & Etr & UC & LTR & BTX & RTOP)|(Etr & TOPLE & SPLT)]; rewrite Etr.
    - eapply (unwind_impl_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (bv_unsigned sp + -2128) 352956 (bv_unsigned sp) ctx t top bot lo (words_of_bytes junk1) ([bv_unsigned ra] ++ tr)).
      all: try lazymatch goal with
         | |- stk _ _ _ _ => rewrite Hsp; exact STa
         | |- mem_inv _ _ => exact MIa
         | |- @eq word _ _ => rewrite ?Esp; first [reflexivity | exact TP | rewrite Z_to_bv_bv_unsigned; reflexivity | apply Z_to_bv_eqm; rewrite ?unsigned_lit by lia; lia]
         | |- ex _ => first [eexists; exact SZC | eexists; exact BPJ]
         | |- u64arr _ _ _ _ => exact TB
         | |- uchain _ _ _ _ _ _ _ => exact (UC1 tr Etr UC BTX)
         | |- _ \/ _ => unboxed CT2
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ (_ + 152) _ => exact CT
         | |- rw_cells _ _ (_ + 8) [C8 _; C8 _] => exact TT
         | |- rw_cells _ _ (_ + 40) _ => exact SW
         | |- rw_cells _ _ (_ + 3168) _ => exact UW
         end.
      all: try eassumption. all: try (unfold AIMG_HI; lia). all: try (Z.div_mod_to_equations; lia).
      all: match goal with |- ?G => idtac "REMU" G end.
    - eapply (unwind_impl_spec0 RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (bv_unsigned sp + -2128) 352956 (bv_unsigned sp) ctx t top bot lo (words_of_bytes junk1)).
      all: try lazymatch goal with
         | |- stk _ _ _ _ => rewrite Hsp; exact STa
         | |- mem_inv _ _ => exact MIa
         | |- @eq word _ _ => rewrite ?Esp; first [reflexivity | exact TP | rewrite Z_to_bv_bv_unsigned; reflexivity | apply Z_to_bv_eqm; rewrite ?unsigned_lit by lia; lia]
         | |- ex _ => first [eexists; exact SZC | eexists; exact BPJ]
         | |- u64arr _ _ _ _ => exact TB
         | |- _ \/ _ => unboxed CT2
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ (_ + 152) _ => exact CT
         | |- rw_cells _ _ (_ + 8) [C8 _; C8 _] => exact TT
         | |- rw_cells _ _ (_ + 40) _ => exact SW
         | |- rw_cells _ _ (_ + 3168) _ => exact UW
         end.
      all: try eassumption. all: try (unfold AIMG_HI; lia). all: try (Z.div_mod_to_equations; lia).
      all: match goal with |- ?G => idtac "REMU0" G end. }
  cbv beta. intros ms2 PU. unfold unwind_impl_post in PU.
  (nd_pre PU 18%nat; intros t0b t1b t2b a0b a1b a2b a3b a4b a5b a6b a7b t3b t4b t5b t6b m2 tb2 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 10%nat; intros MUu WMu MIu STu SZ2 TB2 LTB2 TRF2 BP2 UW2; nd_post).
  unname_sp. rewrite ?unsigned_lit in MUu by lia. rewrite ?unsigned_lit in STu by lia.
  replace (ret_pc (Z_to_bv 64 353048)) with (Z_to_bv 64 353048) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  (* [comment removed for export] *)
  assert (MU12 : munch [(bv_unsigned sp - 2288, bv_unsigned sp - 2128); (bv_unsigned sp - 2120, bv_unsigned sp - 2116); (bv_unsigned sp - 2112, bv_unsigned sp - 64); (t + 3168, t + 3169)]%Z m1 m2).
  { eapply munch_weaken; [| exact MUu]. unfold sub_fp; cbn [outside]; intros q Hq; lia. }
  xport TI MU12 WMu ltac:(lia). xport TK MU12 WMu ltac:(lia). xport T88 MU12 WMu ltac:(lia).
  xport TSD MU12 WMu ltac:(lia). xport CT MU12 WMu ltac:(ub CT2; lia). xport CT8 MU12 WMu ltac:(ub CT2; lia). xport TT0 MU12 WMu ltac:(lia).
  xport FRp MU12 WMu ltac:(lia). xport TAG MU12 WMu ltac:(lia). xport REST MU12 WMu ltac:(lia).
  xport FL1 MU12 WMu ltac:(lia). xport IAS1 MU12 WMu ltac:(lia).
  assert (IAM2 : forall j, 0 <= j < 32768 -> bytes_at asegs m2 (0xaf808 + 8 * j) (le8 (Z_to_bv 64 0))).
  { intros j Hj. eapply bytes_at_agree; [exact (IAM1 j Hj)|].
    intros i Hi. apply MU12. cbn [outside]. rewrite length_le8 in Hi. rewrite wa_unsigned by lia. lia. }
  clear IAM1.
  (* [comment removed for export] *)
  rw_join SZ2 TAG SZT. rw_join FRp SZT SS.
  replace (bv_unsigned sp + -2112) with (bv_unsigned sp + -2128 + 16) in SS by lia.
  rewrite Z_to_bv_bv_unsigned in BP2. rw_join BP2 REST FRS.
  replace (bv_unsigned sp + -2128 + 2056) with (bv_unsigned sp + -72) in FRS by lia.
  (* [comment removed for export] *)
  zstep. zstep. step. step.                                      (* [comment removed for export] *)
  step.                                                          (* [comment removed for export] *)
  name_sp sp (-2128).
  eapply evtF_cut.
  { eapply (dealloc_null_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 lo);
      [rewrite Hsp; exact STu | exact CEIL | rewrite Hsp; lia | exact MIu | reflexivity | rewrite Hsp; eapply rng_sub; [exact RSTK| lia| lia]]. }
  cbv beta. intros ms3 PD.
  (nd_pre PD 17%nat; intros t0c t1c t2c a0c a1c a2c a3c a4c a5c a6c a7c t3c t4c t5c t6c m3 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 4%nat; intros MUd WMd MId STd; nd_post).
  unname_sp. rewrite ?unsigned_lit in MUd by lia. rewrite ?unsigned_lit in STd by lia.
  replace (ret_pc (Z_to_bv 64 353068)) with (Z_to_bv 64 353068) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  xport SS MUd WMd ltac:(lia). xport TB2 MUd WMd ltac:(rewrite LTB2; lia). xport FRS MUd WMd ltac:(lia).
  xport UW2 MUd WMd ltac:(lia). xport FL1 MUd WMd ltac:(lia). xport IAS1 MUd WMd ltac:(lia).
  assert (IAM3 : forall j, 0 <= j < 32768 -> bytes_at asegs m3 (0xaf808 + 8 * j) (le8 (Z_to_bv 64 0))).
  { intros j Hj. eapply bytes_at_agree; [exact (IAM2 j Hj)|].
    intros i Hi. apply MUd. cbn [outside]. rewrite length_le8 in Hi. rewrite wa_unsigned by lia. lia. }
  clear IAM2.
  apply rw_cells_of_u64arr' in TB2. rewrite LTB2 in TB2.
  eapply evtF_mono.
  { (eapply (ficptD_spec RNG sp gp tp); [exact STd | atop_facts; lia | lia | exact MId
      | eexists; split; [exact SS | reflexivity]
      | eexists; split; [replace (bv_unsigned sp + -2112) with (bv_unsigned sp + -2128 + 16) by lia; exact TB2 | reflexivity]
      | exact FRS | exact RIMG | exact RTLS | solve_rng ]). }
  cbv beta. intros ms4 [-> ST4].
  assert (MU : munch [(bv_unsigned sp - 4096, bv_unsigned sp); (0xaf800, 0xaf800 + 0x81030); (0x13e088, 0x13e088 + 4); (t + 3168, t + 3169)]%Z m m3).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUd]].
    eapply munch_trans; [| eapply munch_weaken; [| exact MUu]].
    eapply munch_weaken; [| exact MUa].
    all: unfold sub_fp; cbn [outside]; intros q Hq; lia. }
  assert (WM : wmono asegs m m3).
  { eapply wmono_trans; [exact WMa|]. eapply wmono_trans; [exact WMu| exact WMd]. }
  unfold free_null_post. do 15 eexists. exists m3.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MId|]. split; [exact ST4|].
  split; [exact UW2|]. split; [exact FL1|]. split; [exact IAS1|]. exact IAM3.
  Unshelve. all: try exact STa; try exact STu; try exact STd.
Qed.
End Zd1.
#[using="Type"] Lemma free_null_spec : ltac:(let t := eval cbv delta [free_null_spec__stmt] in free_null_spec__stmt in exact t).
Proof. exact free_null_spec__body. Qed.
End CANSEC1.

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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aunwind.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc1b__A3W.F_aunwind2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_afree_s.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_aintal.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_afree_iseg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_front.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_icpt.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
#[using="Type"] Lemma rw_cells_of_u64arr' : forall m A ws,
  u64arr asegs m A ws -> rw_cells asegs m A [CB (8 * length ws) (u64s ws)].
Proof. exact rw_cells_of_u64arr. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma dealloc_null_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x33934) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST CEIL LO MI -> RSTK. atop_facts.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  word_range sp SPR.
  do 9 step.                                   (* [comment removed for export] *)
  step.                                        (* [comment removed for export] *)
  carve_frame 64%nat ST.
  do 9 step.                                   (* [comment removed for export] *)
  step. if_lit.                                (* [comment removed for export] *)
  do 8 step.                                   (* [comment removed for export] *)
  zstep. step.                                 (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  finish.
Qed.

(* [comment removed for export] *)
Definition free_null_post (sp : word) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 4096, bv_unsigned sp); (0xafc00, 0xafc00 + 0x81030); (0x13e488, 0x13e488 + 4); (t + 3168, t + 3169)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (t + 3168) [C1 (Z_to_bv 8 0)]
    /\ rw_cells asegs m' 0x13e488 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ stk asegs m' 0xafc00 (0xafc00 + 0x81030)
    /\ (forall j, 0 <= j < 32768 -> bytes_at asegs m' (0xafc08 + 8 * j) (le8 (Z_to_bv 64 0))).

Definition free_null_spec__stmt : Prop := forall (ia : bool) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem)
    (t ctx lo top bot : Z) (trt : list Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 0 ->
  bv_unsigned sp mod 16 = 0 ->
  (* [comment removed for export] *)
  allocA_cells m ctx t ->
  rw_cells asegs m 0xa5880 [C8 (Z_to_bv 64 0x140528); C8 (Z_to_bv 64 0xac1f8); C8 (Z_to_bv 64 0xae9f8);
                             C8 (Z_to_bv 64 0xaf6e8); C8 (Z_to_bv 64 0xaf6f0); C8 (Z_to_bv 64 0xaf6e0)] ->
  rw_cells asegs m 0xaf6fc [C4 (Z_to_bv 64 30)] ->
  rw_cells asegs m 0x14054a [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m 0xa5870 [C8 (Z_to_bv 64 0x13e4a0)] -> rw_cells asegs m 0x13e4a0 [C8 (Z_to_bv 64 4096)] ->
  (* [comment removed for export] *)
  rw_cells asegs m 0x13e488 [C1 (Z_to_bv 8 (if ia then 1 else 0)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  stk asegs m 0xafc00 (0xafc00 + 0x81030) ->
  (ia = true -> forall j, 0 <= j < 32768 -> bytes_at asegs m (0xafc08 + 8 * j) (le8 (Z_to_bv 64 0))) ->
  (* [comment removed for export] *)
  rw_cells asegs m (ctx + 8) [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m t [C8 (Z_to_bv 64 ctx); C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)] ->
  rw_cells asegs m (t + 40) [C1 (Z_to_bv 8 0)] -> rw_cells asegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  0 < ctx -> AIMG_HI <= ctx -> ctx + 4096 <= ATOP ->
  iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  (* [comment removed for export] *)
  afree_unw RNG lo m top sp s0 ra trt ->
  bv_unsigned s0 <> bv_unsigned sp + 8 ->
  0 <= bot -> bot < bv_unsigned sp -> bot < top -> 4096 <= top <= 2^47 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  evtF asegs RNG (free_null_post sp ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable ia : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 5).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 6).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 7).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 8).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 9).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 10).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 11).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 12).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 13).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 14).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 15).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 16).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 17).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 18).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 19).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 20).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 21).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 22).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 23).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 24).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 25).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 26).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 27).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 28).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 29).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 30).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 31).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 32).
Variable F : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 33).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 34).
Variable m : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 35).
Variable t : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 36).
Variable ctx : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 37).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 38).
Variable top : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 39).
Variable bot : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 40).
Variable trt : ltac2:(SecDietF.SzSecF.ty 'free_null_spec__stmt 41).
#[using="Type"] Lemma free_null_spec__body : ltac:(let T := type of (fun (h : free_null_spec__stmt) => h ia RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m t ctx lo top bot trt) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (ia, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (t, (ctx, (lo, (top, (bot, trt)))))))))))))))))))))))))))))))))))))))))) as _.

  intros ST CEIL LO MI TP Ha0 SP16 AC GOT6 MCS CF34 GPG PGC FL IAS IAM CT8 TT0 SW UW CX0 C0 C1 T0 T1 CT2
         UNW S0NE B0 BB BOTOP TOP RA4 RANE RIMG RTLS RSTK RCTX RT. band_lin.   (* [comment removed for export] *)
  pose proof (afree_unw_length _ _ _ _ _ _ _ _ UNW) as LTRT.
  pose proof (afree_unw_sp47 _ _ _ _ _ _ _ _ UNW ltac:(clear -TOP; lia)) as SP47.
  pose proof AC as AC'. (nd_pre AC' 8%nat; intros INI RSS IMAX TI TK T88 TSD CT; nd_post).
  unfold AIMG_HI, AINSTANCE, ATP88, ATSD, ATSDI, ATSDK, AINITED, ARSSLIM, GOT_PGSZ, APGSZ, AFREE_SYM, AFREE_PC in *.
  word_range sp SPR. word_range s0 S0R. word_range ra RAR.
  box CT2.
  pose proof TT0 as TTx. rw_split TTx 1%nat TTc TT. clear TTc.
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (ficptA_spec 0 ia RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo);
      try eassumption; try (unfold AIA_FLAG, AIA_BASE, AIA_SIZE, AIA_MAP1; lia).
    all: try lazymatch goal with
         | |- rw_cells _ _ AIA_FLAG _ => exact FL
         | |- stk _ _ AIA_BASE _ => exact IAS
         | |- _ = true -> _ => exact IAM
         | |- rng _ _ _ => solve_rng
         end.
    all: match goal with |- ?G => idtac "REMA" G end. }
  cbv beta. intros ms1 PA. unfold ficptA_post in PA.
  (nd_pre PA 13%nat; intros t0a t1a t2a a6a a7a t3a t4a t5a t6a m1 junk1 junk2 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 10%nat; intros MUa WMa MIa STa FRA FRt FRs FL1 IAS1 IAM1; nd_post).
  (* [comment removed for export] *)
  pose proof FRs as FRs0. rw_split FRs0 7%nat FRsx FRsr. clear FRsx.
  destruct FRsr as [[_ BSR] _]. cbn [cells_bytes cbytes app] in BSR. rewrite app_nil_r in BSR.
  apply bytes_at_app in BSR. destruct BSR as [BS0 BRA]. rewrite length_le8 in BRA.
  replace (bv_unsigned sp + -16 + Z.of_nat 8) with (bv_unsigned sp - 8) in BRA by lia.
  replace (bv_unsigned sp + -16) with (bv_unsigned sp - 16) in BS0 by lia.
  assert (UC1 : forall tr, trt = bv_unsigned ra :: tr -> uchain m top 353060 (bv_unsigned sp) (bv_unsigned s0) 28%nat tr -> bv_unsigned sp + 16 < top ->
                uchain m1 top 353060 bot (bv_unsigned sp) 29%nat ([bv_unsigned ra] ++ tr)).
  { intros tr _ UC BTX. replace ([bv_unsigned ra] ++ tr) with ((if bv_unsigned ra =? 353060 then [] else [bv_unsigned ra]) ++ tr)
      by (replace (bv_unsigned ra =? 353060) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
    eapply (uc_step m1 top 353060 bot (bv_unsigned sp) 29%nat (bv_unsigned s0) (bv_unsigned ra) tr); try lia.
    - rewrite Z_to_bv_bv_unsigned. exact BS0.
    - rewrite Z_to_bv_bv_unsigned. exact BRA.
    - replace (bv_unsigned ra =? 353060) with false by (symmetry; apply Z.eqb_neq; lia). cbn [Nat.pred].
      destruct (Z_le_gt_dec (bv_unsigned sp + 16) (bv_unsigned s0)) as [GE|LT].
      + eapply uchain_frame; [exact UC|]. intros a Ha. apply MUa. cbn [outside]. rewrite unsigned_lit by lia. lia.
      + inversion UC; subst; [apply uc_stop; assumption | exfalso | exfalso]; Z.div_mod_to_equations; lia. }
  clear BS0 BRA.
  (* [comment removed for export] *)
  xport TI MUa WMa ltac:(lia). xport TK MUa WMa ltac:(lia). xport T88 MUa WMa ltac:(lia). xport TSD MUa WMa ltac:(lia).
  xport CT MUa WMa ltac:(lia). xport GPG MUa WMa ltac:(lia). xport PGC MUa WMa ltac:(lia). xport TT MUa WMa ltac:(lia).
  xport TT0 MUa WMa ltac:(lia). xport CT8 MUa WMa ltac:(lia).
  xport SW MUa WMa ltac:(lia). xport UW MUa WMa ltac:(lia). xport INI MUa WMa ltac:(lia).
  pose proof FRA as FRA0. rw_split FRA0 1%nat FRp FRz. rw_split FRz 1%nat SZC TAG.
  change 2040%nat with (8 * 255)%nat in FRt. destruct (u64arr_of_CB _ _ 255%nat _ FRt) as [TB LTB].
  pose proof FRs as FRs1. rw_split FRs1 1%nat BPJ REST.
  replace (bv_unsigned sp + -2120) with (bv_unsigned sp + -2128 + 8) in SZC by lia.
  replace (bv_unsigned sp + -2112) with (bv_unsigned sp + -2128 + 16) in TB by lia.
  replace (bv_unsigned sp + -72) with (bv_unsigned sp + -2128 + 2056) in BPJ by lia.
  (* [comment removed for export] *)
  step.                                                          (* [comment removed for export] *)
  name_sp sp (-2128).
  eapply evtF_cut with (P := unwind_impl_post (bv_unsigned sp + -2128) 353060 (bv_unsigned sp) t _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc lo trt m1).
  { destruct UNW as [(tr & Etr & UC & LTR & BTX & RTOP)|(Etr & TOPLE & SPLT)]; rewrite Etr.
    - eapply (unwind_impl_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (bv_unsigned sp + -2128) 353060 (bv_unsigned sp) ctx t top bot lo (words_of_bytes junk1) ([bv_unsigned ra] ++ tr)).
      all: try lazymatch goal with
         | |- stk _ _ _ _ => rewrite Hsp; exact STa
         | |- mem_inv _ _ => exact MIa
         | |- @eq word _ _ => rewrite ?Esp; first [reflexivity | exact TP | rewrite Z_to_bv_bv_unsigned; reflexivity | apply Z_to_bv_eqm; rewrite ?unsigned_lit by lia; lia]
         | |- ex _ => first [eexists; exact SZC | eexists; exact BPJ]
         | |- u64arr _ _ _ _ => exact TB
         | |- uchain _ _ _ _ _ _ _ => exact (UC1 tr Etr UC BTX)
         | |- _ \/ _ => unboxed CT2
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ (_ + 152) _ => exact CT
         | |- rw_cells _ _ (_ + 8) [C8 _; C8 _] => exact TT
         | |- rw_cells _ _ (_ + 40) _ => exact SW
         | |- rw_cells _ _ (_ + 3168) _ => exact UW
         end.
      all: try eassumption. all: try (unfold AIMG_HI; lia). all: try (Z.div_mod_to_equations; lia).
      all: match goal with |- ?G => idtac "REMU" G end.
    - eapply (unwind_impl_spec0 RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (bv_unsigned sp + -2128) 353060 (bv_unsigned sp) ctx t top bot lo (words_of_bytes junk1)).
      all: try lazymatch goal with
         | |- stk _ _ _ _ => rewrite Hsp; exact STa
         | |- mem_inv _ _ => exact MIa
         | |- @eq word _ _ => rewrite ?Esp; first [reflexivity | exact TP | rewrite Z_to_bv_bv_unsigned; reflexivity | apply Z_to_bv_eqm; rewrite ?unsigned_lit by lia; lia]
         | |- ex _ => first [eexists; exact SZC | eexists; exact BPJ]
         | |- u64arr _ _ _ _ => exact TB
         | |- _ \/ _ => unboxed CT2
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ (_ + 152) _ => exact CT
         | |- rw_cells _ _ (_ + 8) [C8 _; C8 _] => exact TT
         | |- rw_cells _ _ (_ + 40) _ => exact SW
         | |- rw_cells _ _ (_ + 3168) _ => exact UW
         end.
      all: try eassumption. all: try (unfold AIMG_HI; lia). all: try (Z.div_mod_to_equations; lia).
      all: match goal with |- ?G => idtac "REMU0" G end. }
  cbv beta. intros ms2 PU. unfold unwind_impl_post in PU.
  (nd_pre PU 18%nat; intros t0b t1b t2b a0b a1b a2b a3b a4b a5b a6b a7b t3b t4b t5b t6b m2 tb2 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 10%nat; intros MUu WMu MIu STu SZ2 TB2 LTB2 TRF2 BP2 UW2; nd_post).
  unname_sp. rewrite ?unsigned_lit in MUu by lia. rewrite ?unsigned_lit in STu by lia.
  replace (ret_pc (Z_to_bv 64 353152)) with (Z_to_bv 64 353152) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  (* [comment removed for export] *)
  assert (MU12 : munch [(bv_unsigned sp - 2288, bv_unsigned sp - 2128); (bv_unsigned sp - 2120, bv_unsigned sp - 2116); (bv_unsigned sp - 2112, bv_unsigned sp - 64); (t + 3168, t + 3169)]%Z m1 m2).
  { eapply munch_weaken; [| exact MUu]. unfold sub_fp; cbn [outside]; intros q Hq; lia. }
  xport TI MU12 WMu ltac:(lia). xport TK MU12 WMu ltac:(lia). xport T88 MU12 WMu ltac:(lia).
  xport TSD MU12 WMu ltac:(lia). xport CT MU12 WMu ltac:(ub CT2; lia). xport CT8 MU12 WMu ltac:(ub CT2; lia). xport TT0 MU12 WMu ltac:(lia).
  xport FRp MU12 WMu ltac:(lia). xport TAG MU12 WMu ltac:(lia). xport REST MU12 WMu ltac:(lia).
  xport FL1 MU12 WMu ltac:(lia). xport IAS1 MU12 WMu ltac:(lia).
  assert (IAM2 : forall j, 0 <= j < 32768 -> bytes_at asegs m2 (0xafc08 + 8 * j) (le8 (Z_to_bv 64 0))).
  { intros j Hj. eapply bytes_at_agree; [exact (IAM1 j Hj)|].
    intros i Hi. apply MU12. cbn [outside]. rewrite length_le8 in Hi. rewrite wa_unsigned by lia. lia. }
  clear IAM1.
  (* [comment removed for export] *)
  rw_join SZ2 TAG SZT. rw_join FRp SZT SS.
  replace (bv_unsigned sp + -2112) with (bv_unsigned sp + -2128 + 16) in SS by lia.
  rewrite Z_to_bv_bv_unsigned in BP2. rw_join BP2 REST FRS.
  replace (bv_unsigned sp + -2128 + 2056) with (bv_unsigned sp + -72) in FRS by lia.
  (* [comment removed for export] *)
  zstep. zstep. step. step.                                      (* [comment removed for export] *)
  step.                                                          (* [comment removed for export] *)
  name_sp sp (-2128).
  eapply evtF_cut.
  { eapply (dealloc_null_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 lo);
      [rewrite Hsp; exact STu | exact CEIL | rewrite Hsp; lia | exact MIu | reflexivity | rewrite Hsp; eapply rng_sub; [exact RSTK| lia| lia]]. }
  cbv beta. intros ms3 PD.
  (nd_pre PD 17%nat; intros t0c t1c t2c a0c a1c a2c a3c a4c a5c a6c a7c t3c t4c t5c t6c m3 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 4%nat; intros MUd WMd MId STd; nd_post).
  unname_sp. rewrite ?unsigned_lit in MUd by lia. rewrite ?unsigned_lit in STd by lia.
  replace (ret_pc (Z_to_bv 64 353172)) with (Z_to_bv 64 353172) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  xport SS MUd WMd ltac:(lia). xport TB2 MUd WMd ltac:(rewrite LTB2; lia). xport FRS MUd WMd ltac:(lia).
  xport UW2 MUd WMd ltac:(lia). xport FL1 MUd WMd ltac:(lia). xport IAS1 MUd WMd ltac:(lia).
  assert (IAM3 : forall j, 0 <= j < 32768 -> bytes_at asegs m3 (0xafc08 + 8 * j) (le8 (Z_to_bv 64 0))).
  { intros j Hj. eapply bytes_at_agree; [exact (IAM2 j Hj)|].
    intros i Hi. apply MUd. cbn [outside]. rewrite length_le8 in Hi. rewrite wa_unsigned by lia. lia. }
  clear IAM2.
  apply rw_cells_of_u64arr' in TB2. rewrite LTB2 in TB2.
  eapply evtF_mono.
  { (eapply (ficptD_spec RNG sp gp tp); [exact STd | atop_facts; lia | lia | exact MId
      | eexists; split; [exact SS | reflexivity]
      | eexists; split; [replace (bv_unsigned sp + -2112) with (bv_unsigned sp + -2128 + 16) by lia; exact TB2 | reflexivity]
      | exact FRS | exact RIMG | exact RTLS | solve_rng ]). }
  cbv beta. intros ms4 [-> ST4].
  assert (MU : munch [(bv_unsigned sp - 4096, bv_unsigned sp); (0xafc00, 0xafc00 + 0x81030); (0x13e488, 0x13e488 + 4); (t + 3168, t + 3169)]%Z m m3).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUd]].
    eapply munch_trans; [| eapply munch_weaken; [| exact MUu]].
    eapply munch_weaken; [| exact MUa].
    all: unfold sub_fp; cbn [outside]; intros q Hq; lia. }
  assert (WM : wmono asegs m m3).
  { eapply wmono_trans; [exact WMa|]. eapply wmono_trans; [exact WMu| exact WMd]. }
  unfold free_null_post. do 15 eexists. exists m3.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MId|]. split; [exact ST4|].
  split; [exact UW2|]. split; [exact FL1|]. split; [exact IAS1|]. exact IAM3.
  Unshelve. all: try exact STa; try exact STu; try exact STd.
Qed.
End Zd1.
#[using="Type"] Lemma free_null_spec : ltac:(let t := eval cbv delta [free_null_spec__stmt] in free_null_spec__stmt in exact t).
Proof. exact free_null_spec__body. Qed.
End CANSEC1.
End TwB.
End F_afree_null.
