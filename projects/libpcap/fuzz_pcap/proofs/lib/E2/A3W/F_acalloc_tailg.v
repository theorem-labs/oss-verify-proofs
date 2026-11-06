(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecSlog__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_agbb__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3 F_aunwind. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_s__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_acalloc_iseg__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3g0__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3g. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_aalloc2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aunwind OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc__A3W.F_aalloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_amalloc_iseg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc__A3W.F_amalloc_icpt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_iseg__A3W.F_acalloc_iseg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_aalloc2g0 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3g0__A3W.F_aalloc3g0 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_aalloc2g OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3g.
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
(* [comment removed for export] *)
Local Ltac hide_disj_all := repeat match goal with H : (_ \/ _) |- _ => change (?P) with (sf_hide P) in H end.
Local Ltac hide_disj_but X :=
  repeat match goal with H : (_ \/ _) |- _ => tryif constr_eq H X then fail else change (?P) with (sf_hide P) in H end.
Local Ltac lia_rel := first [ solve [ hide_disj_all; lia ] | match goal with X : (_ \/ _) |- _ => solve [ hide_disj_but X; lia ] end ].
(* [comment removed for export] *)
From Ltac2 Require Import Ltac2.
Local Ltac2 rlx_prune (x : ident) : unit :=
  let hs := Control.hyps () in
  let cs := zt_plain_consts () in
  let ids := List.map_filter (fun h => let (id, body, ty) := h in
                match body with
                | Some _ => None
                | None => if Ident.equal id x then None else if zt_plain_arith_s cs ty then None
                          else if zt_is_local id then zt_is_prop_some ty id else None
                end) hs in
  match ids with [] => () | _ :: _ => Std.clear ids end.
Local Ltac2 rlx_id (v : Ltac1.t) : ident :=
  match Ltac1.to_ident v with
  | Some id => id
  | None => match Constr.Unsafe.kind (Option.get (Ltac1.to_constr v)) with Constr.Unsafe.Var id => id | _ => Control.throw (Tactic_failure None) end
  end.
Set Default Proof Mode "Classic".
Local Ltac rlx_prune X := let f := ltac2:(x |- rlx_prune (rlx_id x)) in f X.
Local Ltac rlx_lia X := rlx_prune X; first [ zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac lia_rel ::= first [ solve [ hide_disj_all; lia ] | match goal with X : (_ \/ _) |- _ => solve [ hide_disj_but X; rlx_lia X ] end ].
Local Ltac lia_relc := repeat split; first [ lia_rel | lia ].
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
Local Ltac fp_cheap8 := first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs end | clear ]; Stdlib.micromega.Lia.lia.   (* [comment removed for export] *)
Local Ltac fp_find8c := first [ apply Exists_cons_hd; cbn [fst snd]; split; fp_cheap8 | apply Exists_cons_tl; fp_find8c ].
Local Ltac fp_find8 := first [ apply Exists_cons_hd; cbn [fst snd]; split; lia | apply Exists_cons_tl; fp_find8 ].
Local Ltac fp_cover8 := apply sub_fp_cover8; repeat (apply Forall_cons; [ cbn [fst snd]; first [left; fp_cheap8 | right; fp_find8c | right; fp_find8] | ]); apply Forall_nil.
(* [comment removed for export] *)
Local Ltac transport_call_munch_tac ::= first [ fp_cover8 | unfold sub_fp; cbn [outside]; first [ match goal with Hs : bv_unsigned _ = bv_unsigned _ + _ |- _ => clear -Hs; intros; lia end | clear; intros; lia | intros; slia ] ].
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
(* [comment removed for export] *)
#[using="Type"] Local Lemma ablk_int : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6303744 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
#[using="Type"] Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
#[using="Type"] Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6303744 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
(* [comment removed for export] *)
#[using="Type"] Local Lemma ablk_shad_int : forall a ms, ablk a (a + ms) -> a mod 8 = 0 -> 0 <= ms ->
  exists k, 0 <= k <= 1 /\ a + ms <= shad a + k * 18446744073709551616 /\ shad a + ms / 8 + 8 <= a + (1 - k) * 18446744073709551616
            /\ 2148238848 <= shad a /\ shad a + ms / 8 <= 17594333495296.
Proof.
  intros a ms H A8 M0. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. rewrite !Shadow.shad_div. unfold AsanEmbed.ASHOFF.
  destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; Z.div_mod_to_equations; lia.
Qed.
Section WithDepot.
Variable DI : ADepotIface.

Notation malloc_W L sp t c AB UB PG pgw n :=
  ([(bv_unsigned sp - 4096, bv_unsigned sp); (t + 208 + c * 80, t + 208 + c * 80 + 4); (t + 2784, t + 2792);
    (t + 2800, t + 3168); (t + 3168, t + 3169); (UB - 16, UB + n); (AB, AB + 16);
    (shad UB, shad UB + shlen (n - n mod 8)); (PG, PG + pgw);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z) (only parsing).

(* [comment removed for export] *)
Definition malloc_post_genU (L : alayout) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (n t c cnt AB UB PG pgw lo b1 : Z) (maxc csz : word) (ub : list byte) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (id : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (sj' : list word) (stj' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 UB) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (malloc_W L sp t c AB UB PG pgw n) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ 0 < id < 2^31
    /\ rw_cells asegs m' (t + 208 + c * 80) [C4 (Z_to_bv 64 (cnt - 1)); C4 maxc; C8 csz]
    /\ rw_cells asegs m' (t + 2784) [C8 stj']
    /\ u64arr asegs m' (t + 2800) sj' /\ length sj' = 46%nat
    /\ rw_cells asegs m' (t + 3168) [C1 (Z_to_bv 8 0)]
    /\ rw_cells asegs m' (UB + -16) [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 (Z.lor (Z.land (hdr_b1_mid b1) 243) 0)); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)]
    /\ rw_cells asegs m' UB [CB (Z.to_nat n) ub]
    /\ (16 < rz_size n -> rw_cells asegs m' AB [C8 (Z_to_bv 64 0xCC6E96B9CC6E96B9); C8 (Z_to_bv 64 (UB + -16))])
    /\ rw_cells asegs m' (shad UB) [CB (Z.to_nat (shlen (n - n mod 8))) (repeat (Z_to_bv 8 0) (Z.to_nat (shlen (n - n mod 8))))]
    /\ (n mod 8 <> 0 -> rw_cells asegs m' PG [C1 (Z_to_bv 8 (n mod 8))])
    /\ ADEPOT DI L m'.

Definition calloc_tail_gen__stmt : Prop := forall (L : alayout) RNG (ra sp gp tp spA : word) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s4A s5A s6A s3i s2i s1i s0i : word)
    (F : bvmap 5 word) fc (m : amem)
    (n t c cnt AB UB PG pgw lo b0 b1 szh szl ctxj sz SB : Z) (maxc csz stj j1 j2 : word) (pj : byte)
    (sj : list word) (sjunk uj fr0 frc junk0 junk2 : list byte) (tb : list word) (tr : list Z),
  let ctx := al_ctx L in
  bv_unsigned spA = bv_unsigned sp - 2192 ->
  stk asegs m lo (bv_unsigned sp - 2320) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  1 <= n -> is_primary n = true ->
  (* [comment removed for export] *)
  allocA_cells m ctx t -> poison_cells m ->
  rw_cells asegs m 0xabe4d [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m 0xabe24 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->
  rw_cells asegs m 0xa6108 [C8 (Z_to_bv 64 0x10)] -> rw_cells asegs m (ATPv + 16) [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m 0x1400c0 [C8 (Z_to_bv 64 0)] ->
  (* [comment removed for export] *)
  rw_cells asegs m (ctx + 8) [C4 (Z_to_bv 64 0)] -> rw_cells asegs m t [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> sclr ctx 65536 ->
  iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> t mod 4096 = 0 -> sclr t 4096 ->
  (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  (* [comment removed for export] *)
  class_id (needed_size n) = c ->
  rw_cells asegs m (t + 208 + c * 80) [C4 (Z_to_bv 64 (cnt - 1)); C4 maxc; C8 csz] ->
  rw_cells asegs m (t + 2784) [C8 stj] ->
  (* [comment removed for export] *)
  UB = AB + rz_size n -> 0x10007fff8000 <= AB -> UB + (size_of_class (class_id (needed_size n)) - rz_size n) <= ATOP -> AB mod 16 = 0 ->
  needed_size n <= size_of_class (class_id (needed_size n)) <= 65536 ->
  PG = shad UB + shlen (n - n mod 8) -> pgw = (if n mod 8 =? 0 then 0 else 1) ->
  0x2008fff7000 <= shad AB -> shad AB + 2 <= shad UB -> 0 <= shlen (n - n mod 8) <= 8192 -> PG + 1 <= 0x10007fff8000 ->
  rw_cells asegs m (UB + -16) [C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 szh); C4 (Z_to_bv 64 szl); C8 (Z_to_bv 64 ctxj)] ->
  0 <= b1 < 256 ->
  rw_cells asegs m UB [CB (Z.to_nat n) uj] ->
  (16 < rz_size n -> rw_cells asegs m AB [C8 j1; C8 j2]) ->
  rw_cells asegs m (shad AB) [C1 (Z_to_bv 8 0xfa)] ->
  rw_cells asegs m (shad UB) [CB (Z.to_nat (shlen (n - n mod 8))) sjunk] ->
  (n mod 8 <> 0 -> rw_cells asegs m PG [C1 pj]) ->
  (* [comment removed for export] *)
  (t + 4096 <= AB \/ AB + 65536 <= t) -> (ctx + 4096 <= AB \/ AB + 65536 <= ctx) ->
  (al_nodes L + 1048576 <= AB \/ AB + 65536 <= al_nodes L) -> (al_store L + 8388608 <= AB \/ AB + 65536 <= al_store L) -> tclr AB 65536 ->
  (t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) -> (t + 4096 <= al_store L \/ al_store L + 8388608 <= t) ->
  (ctx + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= ctx) -> (ctx + 4096 <= al_store L \/ al_store L + 8388608 <= ctx) -> tclr (al_nodes L) 1048576 -> tclr (al_store L) 8388608 ->
  sclr (al_nodes L) 1048576 -> al_nodes L + 1048576 <= ATOP -> sclr (al_store L) 8388608 -> al_store L + 8388608 <= ATOP ->
  (* [comment removed for export] *)
  rw_cells asegs m (bv_unsigned sp - 2320)
     [CB 8 fr0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 16); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6A; C8 s5A;
      C8 s4A; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 AINSTANCE); C8 (Z_to_bv 64 (bv_unsigned sp + -2136)); C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 0x345e4)] ->
  rw_cells asegs m (bv_unsigned sp + -2192) [CB 8 frc; C8 s3i; C8 s2i; C8 s1i; C8 s0i; C8 (Z_to_bv 64 0x566c0)] ->
  rw_cells asegs m (bv_unsigned sp + -2144) [CB 8 junk0] ->
  (* [comment removed for export] *)
  rw_cells asegs m (AINSTANCE + 32) [C8 (Z_to_bv 64 SB)] -> 0 <= SB -> SB <= UB -> UB < SB + 137438953472 -> SB + 137438953472 < 2^64 ->
  rw_cells asegs m (bv_unsigned sp + -2136) [C8 (Z_to_bv 64 (bv_unsigned sp + -2136 + 16)); C8 (Z_to_bv 64 sz)] ->
  sz = 1 + Z.of_nat (length tr) -> sz <= 255 ->
  u64arr asegs m (bv_unsigned sp + -2136 + 16) tb -> length tb = 255%nat ->
  map bv_unsigned (firstn (Datatypes.S (length tr)) tb) = ACALLOC_PC :: tr ->
  In (ACALLOC_PC :: tr) (al_U L) -> bv_unsigned sp < 2^47 ->
  rw_cells asegs m (bv_unsigned sp + -80) [C8 sp; CB 8 junk2; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ADEPOT DI L m ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 ->
  rng RNG (UB - 16) (n + 16) -> rng RNG AB 16 -> rng RNG (shad AB) 1 -> rng RNG (shad UB) (shlen (n - n mod 8)) -> (n mod 8 <> 0 -> rng RNG PG 1) ->
  AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L ->      (* [comment removed for export] *)
  evtF asegs RNG (malloc_post_genU L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n t c cnt AB UB PG pgw lo b1 maxc csz (repeat (Z_to_bv 8 0) (Z.to_nat n)) m)
    (MS (mkR (Z_to_bv 64 0x33ea8) (Z_to_bv 64 (bv_unsigned spA + -128)) gp tp t0 t1 t2
             (Z_to_bv 64 1) (Z_to_bv 64 n) (Z_to_bv 64 AB) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 8) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n)
             (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 t) (Z_to_bv 64 1)
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x33ea8) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 5).
Variable spA : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 6).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 7).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 8).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 9).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 10).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 11).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 12).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 13).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 14).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 15).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 16).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 17).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 18).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 19).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 20).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 21).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 22).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 23).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 24).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 25).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 26).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 27).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 28).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 29).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 30).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 31).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 32).
Variable s4A : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 33).
Variable s5A : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 34).
Variable s6A : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 35).
Variable s3i : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 36).
Variable s2i : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 37).
Variable s1i : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 38).
Variable s0i : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 39).
Variable F : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 40).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 41).
Variable m : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 42).
Variable n : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 43).
Variable t : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 44).
Variable c : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 45).
Variable cnt : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 46).
Variable AB : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 47).
Variable UB : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 48).
Variable PG : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 49).
Variable pgw : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 50).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 51).
Variable b0 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 52).
Variable b1 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 53).
Variable szh : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 54).
Variable szl : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 55).
Variable ctxj : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 56).
Variable sz : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 57).
Variable SB : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 58).
Variable maxc : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 59).
Variable csz : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 60).
Variable stj : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 61).
Variable j1 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 62).
Variable j2 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 63).
Variable pj : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 64).
Variable sj : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 65).
Variable sjunk : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 66).
Variable uj : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 67).
Variable fr0 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 68).
Variable frc : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 69).
Variable junk0 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 70).
Variable junk2 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 71).
Variable tb : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 72).
Variable tr : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 73).
#[using="Type"] Lemma calloc_tail_gen__body : ltac:(let T := type of (fun (h : calloc_tail_gen__stmt) => h L RNG ra sp gp tp spA t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s4A s5A s6A s3i s2i s1i s0i F fc m n t c cnt AB UB PG pgw lo b0 b1 szh szl ctxj sz SB maxc csz stj j1 j2 pj sj sjunk uj fr0 frc junk0 junk2 tb tr) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (ra, (sp, (gp, (tp, (spA, (t0, (t1, (t2, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (t3, (t4, (t5, (t6, (s0, (s1, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (s4A, (s5A, (s6A, (s3i, (s2i, (s1i, (s0i, (F, (fc, (m, (n, (t, (c, (cnt, (AB, (UB, (PG, (pgw, (lo, (b0, (b1, (szh, (szl, (ctxj, (sz, (SB, (maxc, (csz, (stj, (j1, (j2, (pj, (sj, (sjunk, (uj, (fr0, (frc, (junk0, (junk2, (tb, tr)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) as _.
 cbv zeta.
  intros HspA ST CEIL LO MI TP N PRIM AC PC PP FLG HK MCS CF34 CX8 TT0 UW STATS LSJ CX0 CX1 CXS T0 T1 TAL TS CT2
         HC CRa STSa HUB ABLO UBHI AB16 NSZ HPG HPW SB1 SB2 SB3 SB4 HDR B1 UJ LH SHA SHU SHP
         DJT DJC DJN DJS XTAB DTN DTS DCN DCS XTNO XTST N0 N1 R0 R1 FRa FR16 FRP INST PSB0 PSB1 PSB2 PSB3 SS SZ SZB TB LTB TRF TRU S47 FRS DEP
         RIMG RTLS RSTK RCTX RT RNO RST RU RAB RSA RSU RSP NI SI. band_lin.   (* [comment removed for export] *)
  unfold AIMG_HI in CX0, NI, SI.
  (nd_pre (sclr_int _ _ TS ltac:(clear -T0; lia) ltac:(clear -T1; lia)) 4%nat; intros kT TBND TBNDa TBNDb; nd_post).   (* [comment removed for export] *)
  (nd_pre (sclr_int _ _ CXS ltac:(clear -CX0; lia) ltac:(clear -CX1; lia)) 4%nat; intros kC CBND CBNDa CBNDb; nd_post).
  (nd_pre (sclr_int _ _ N0 ltac:(clear -NI; lia) ltac:(clear -N1; lia)) 4%nat; intros kN NBND NBNDa NBNDb; nd_post).
  (nd_pre (sclr_int _ _ R0 ltac:(clear -SI; lia) ltac:(clear -R1; lia)) 4%nat; intros kR SBND SBNDa SBNDb; nd_post).
  assert (PW01 : 0 <= pgw <= 1) by (rewrite HPW; destruct (n mod 8 =? 0); lia).
  (pose proof (prim_facts n N PRIM) as ndP__; nd_pre ndP__ 8%nat; intros NS RZR RZE RZM RLR RSR RSM NSR; nd_post).
  (pose proof (prim_class_facts n c N PRIM HC) as ndP__; nd_pre ndP__ 5%nat; intros C16 NSZ2 SM16 SMALL MC2; nd_post).
  (* [comment removed for export] *)
  destruct (tclr_int_lem _ _ XTAB ltac:(clear -ABLO; lia) ltac:(clear -UBHI HUB NSZ NS RZR RSR; pose proof atop_range; lia)) as (kLA & LABND).
  destruct (tclr_int_lem _ _ XTNO ltac:(clear -NI; lia) ltac:(clear -N1; pose proof atop_range; lia)) as (kLN & LNBND).
  destruct (tclr_int_lem _ _ XTST ltac:(clear -SI; lia) ltac:(clear -R1; pose proof atop_range; lia)) as (kLS & LSBND).
  pose proof AC as AC'. (nd_pre AC' 8%nat; intros INI RSS IMAX TI TK T88 TSD CT; nd_post).
  unfold AIMG_HI, AINSTANCE, ATP88, ATSD, ATSDI, ATSDK, AINITED, ARSSLIM, ACALLOC_PC in *. change (700312 + 32) with 700344 in INST.
  word_range sp SPR.
  box DJT. box DJC. box DJN. box DJS. box DTN. box DTS. box DCN. box DCS. box CT2.
  (* [comment removed for export] *)
  replace (bv_unsigned sp - 2320) with (bv_unsigned spA + -128) in ST, FRa by lia.
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (allocBC_gen0 DI L RNG spA gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m n (bv_unsigned sp + -2136) t AB UB PG pgw lo b0 b1 szh szl ctxj sz 353872 pj sjunk tb tr fr0 _ _ _ _ _ _ _ _ _ _ _ _ _).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact ST
         | |- mem_inv _ _ => exact MI
         | |- poison_cells _ => exact PC
         | |- ADEPOT _ _ _ => exact DEP
         | |- @eq word _ _ => first [reflexivity | exact TP]
         | |- u64arr _ _ _ _ => exact TB
         | |- _ \/ _ => first [unboxed DJT | unboxed DJC | unboxed DJN | unboxed DJS]
         | |- rng _ _ _ => solve_rng
         | |- ~ _ -> _ => exact SHP
         | |- _ -> rw_cells _ _ _ _ => exact LH
         end.
    all: try eassumption. all: try (unfold AIMG_HI; lia).
    all: match goal with |- ?G => idtac "REMBC" G end. }
  cbv beta. intros ms2 PB. unfold allocBC_postG in PB.
  (nd_pre PB 20%nat; intros id raB t0b t1b t2b a0b a1b a2b a3b a4b a5b a6b a7b s6b t3b t4b t5b t6b m2 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 9%nat; intros MUb WMb MIb STb IDR HDRb SHUb SHPb DEPb; nd_post).
  rewrite ?HspA in MUb.
  (* [comment removed for export] *)
  xport FRP MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia). xport INST MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia).
  xport FRa MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia).
  xport STATS MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; ub DTN; ub DTS; lia_relc).   (* [comment removed for export] *)
  xport TI MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia). xport TK MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia). xport T88 MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia). xport TSD MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia).
  xport CT MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJC; ub DCN; ub DCS; lia_relc).
  xport FLG MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia). xport HK MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia). xport MCS MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia). xport CF34 MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia).
  pose proof PC as PC'. (nd_pre PC' 7%nat; intros GOT GOT80 REAL PC4 PC5 PC6 PC7; nd_post).
  xport GOT MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia). xport GOT80 MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia). xport REAL MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia).
  xport PC4 MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia). xport PC5 MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia).
  xport UJ MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJN; ub DJS; lia_relc).
  xport CRa MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; ub DTN; ub DTS; lia_relc). xport STSa MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; ub DTN; ub DTS; lia_relc).
  xport UW MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; ub DTN; ub DTS; lia_relc).
  xport FR16 MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia). xport SS MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia). xport FRS MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia).
  xport TB MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; rewrite LTB; lia).
  assert (LH2 : 16 < rz_size n -> rw_cells asegs m2 AB [C8 j1; C8 j2]).
  { intros RZ. specialize (LH RZ). pose proof (rz_size_cases n) as RZC.
    xport LH MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS RZ RZC; ub DJN; ub DJS; lia_relc). exact LH. }
  clear LH SHP.
  pose proof (hdr_b1_mid_range b1 ltac:(lia)) as B1M.
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (allocD_gen0 L RNG spA gp tp F fc m2 n t c AB UB lo b0 (hdr_b1_mid b1) id (bv_unsigned sp + -2136) sj uj j1 j2 fr0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact STb
         | |- mem_inv _ _ => exact MIb
         | |- @eq word _ _ => first [reflexivity | exact TP]
         | |- u64arr _ _ _ _ => exact STATS
         | |- _ \/ _ => first [unboxed DJT | unboxed DJC | unboxed DJN | unboxed DJS]
         | |- rng _ _ _ => solve_rng
         | |- _ -> rw_cells _ _ _ _ => exact LH2
         | |- rw_cells _ _ (_ + 152) _ => exact CT
         | |- rw_cells _ _ (_ + -16) _ => exact HDRb
         | |- tclr _ _ => apply (tclr_sub AB 65536); [exact XTAB | clear; lia | clear -HUB NSZ NS RZR RSR N; lia]      (* [comment removed for export] *)
         end.
    all: try eassumption. all: try (unfold AIMG_HI; lia).
    all: match goal with |- ?G => idtac "REMD" G end. }
  cbv beta. intros ms3 PD. unfold allocD_postG0 in PD.
  (nd_pre PD 17%nat; intros t0d t1d t2d a1d a2d a3d a4d a5d a6d a7d t3d t4d t5d t6d m3 sj3 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 9%nat; intros MUd WMd MId STd STATSd LSJd UFd HDRd LHd; nd_post).
  rewrite ?HspA in MUd.
  xport CRa MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; ylia). xport STSa MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; ylia).
  xport SHUb MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia). xport UW MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; ylia).   (* [comment removed for export] *)
  xport FRP MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia). xport INST MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia). xport GOT80 MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia). xport REAL MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia).
  xport FR16 MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia). xport SS MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia). xport FRS MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia). xport TB MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; rewrite LTB; lia).
  assert (SHPd : n mod 8 <> 0 -> rw_cells asegs m3 PG [C1 (Z_to_bv 8 (n mod 8))]).
  { intros NE. specialize (SHPb NE). xport SHPb MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS NE; lia). exact SHPb. }
  assert (LH4 : 16 < rz_size n -> rw_cells asegs m3 AB [C8 (Z_to_bv 64 0xCC6E96B9CC6E96B9); C8 (Z_to_bv 64 (UB + -16))]).
  { intros RZ. exact (LHd RZ). }
  assert (DEPd : ADEPOT DI L m3).
  { eapply (adi_frame DI); [exact DEPb | exact MUd | exact WMd |].
    repeat (apply Forall_cons; [cbn [fst snd]; intros a Ha; first [clear -Ha HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RSR NSR HPG PW01 SB1 SB2 SB3 SB4 C16 LSJ N DTN DTS DJN DJS; ub DTN; ub DTS; ub DJN; ub DJS; ylia | ub DTN; ub DTS; ub DJN; ub DJS; ylia]|]). apply Forall_nil. }   (* [comment removed for export] *)
  (* [comment removed for export] *)
  replace (ret_pc (Z_to_bv 64 0x345e4)) with (Z_to_bv 64 0x345e4) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  assert (EspA : spA = Z_to_bv 64 (bv_unsigned sp + -2192)).
  { enough (E : Z_to_bv 64 (bv_unsigned spA) = Z_to_bv 64 (bv_unsigned sp + -2192)) by (rewrite Z_to_bv_bv_unsigned in E; exact E).
    apply Z_to_bv_eqm. rewrite HspA. zeq. }
  rewrite EspA. rewrite HspA in STd. replace (bv_unsigned sp - 2192) with (bv_unsigned sp + -2192) in STd by lia.
  apply rw_cells_of_u64arr in TB. rewrite LTB in TB.
  eapply evtF_cut.
  { eapply (cicptC_spec RNG sp gp tp) with (SB := SB) (n := n) (uj := uj);
      [exact STd | atop_facts; lia | lia | exact MId | clear -ABLO HUB RZR; lia | exact N | clear -UBHI CEIL HUB NSZ NS RZR RSR N; atop_facts; lia
      | exact PSB0 | exact PSB1 | exact PSB2 | exact PSB3 | exact INST | exact GOT80 | exact REAL | exact UFd | exact FR16
      | eexists; split; [exact FRP | reflexivity]
      | eexists; split; [exact SS | reflexivity]
      | eexists; split; [replace (bv_unsigned sp + -2120) with (bv_unsigned sp + -2136 + 16) by lia; exact TB | reflexivity]
      | exact FRS | exact RIMG | exact RTLS | solve_rng | eapply rng_sub'; [exact RU | clear -N; lia] ]. }
  cbv beta. intros ms5 PCC. unfold cicptC_post in PCC.
  (nd_pre PCC 16%nat; intros t0e t1e t2e a1e a2e a3e a4e a5e a6e a7e t3e t4e t5e t6e m5 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 5%nat; intros MUc WMc MIc STc UZ; nd_post).
  apply evtF_done.
  (* [comment removed for export] *)
  xport CRa MUc WMc ltac:(first [clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT; ub DJT; ylia | ub DJT; ylia]). xport STSa MUc WMc ltac:(first [clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT; ub DJT; ylia | ub DJT; ylia]). xport STATSd MUc WMc ltac:(rewrite ?upd_length; first [clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT; ub DJT; ylia | ub DJT; ylia]).
  xport HDRd MUc WMc ltac:(first [clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT; ub DJT; ylia | ub DJT; ylia]). clear UFd. xport SHUb MUc WMc ltac:(first [clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT; ub DJT; ylia | ub DJT; ylia]). xport UW MUc WMc ltac:(first [clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT; ub DJT; ylia | ub DJT; ylia]).
  assert (LH5 : 16 < rz_size n -> rw_cells asegs m5 AB [C8 (Z_to_bv 64 0xCC6E96B9CC6E96B9); C8 (Z_to_bv 64 (UB + -16))]).
  { intros RZ. specialize (LH4 RZ). pose proof (rz_size_cases n) as RZC. xport LH4 MUc WMc ltac:(first [clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT RZC; ub DJT; ylia | ub DJT; ylia]). exact LH4. }
  assert (SHP5 : n mod 8 <> 0 -> rw_cells asegs m5 PG [C1 (Z_to_bv 8 (n mod 8))]).
  { intros NE. specialize (SHPd NE). xport SHPd MUc WMc ltac:(first [clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT; ub DJT; ylia | ub DJT; ylia]). exact SHPd. }
  assert (DEP5 : ADEPOT DI L m5).
  { eapply (adi_frame DI); [exact DEPd | exact MUc | exact WMc |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; first [clear -Ha HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RSR NSR HPG PW01 SB1 SB2 SB3 SB4 C16 LSJ N DTN DTS DJN DJS; ub DTN; ub DTS; ub DJN; ub DJS; ylia | ub DTN; ub DTS; ub DJN; ub DJS; ylia] | apply Forall_nil]. }
  assert (MU : munch (malloc_W L sp t c AB UB PG pgw n) m m5).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUc]].
    eapply munch_trans; [| eapply munch_weaken; [| exact MUd]].
    eapply munch_weaken; [| exact MUb].
    all: first [clear -N C16 PW01 HspA; unfold sub_fp; cbn [outside]; intros q Hq; lia | fp_cover8 | unfold sub_fp; cbn [outside]; intros q Hq; lia]. }   (* [comment removed for export] *)
  assert (WM : wmono asegs m m5).
  { eapply wmono_trans; [exact WMb|]. eapply wmono_trans; [exact WMd| exact WMc]. }
  unfold malloc_post_genU. exists id. do 14 eexists. exists m5, sj3, stj. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MIc|]. split; [exact STc|]. split; [exact IDR|].
  split; [exact CRa|]. split; [exact STSa|]. split; [exact STATSd|]. split; [exact LSJd|]. split; [exact UW|].
  split; [exact HDRd|]. split; [exact UZ|]. split; [exact LH5|]. split; [exact SHUb|]. split; [exact SHP5|]. exact DEP5.
  Unshelve. all: try exact STb; try exact ST.
Qed.
End Zd1.
#[using="Type"] Lemma calloc_tail_gen : ltac:(let t := eval cbv delta [calloc_tail_gen__stmt] in calloc_tail_gen__stmt in exact t).
Proof. exact calloc_tail_gen__body. Qed.
End WithDepot.
End CANSEC1.
(* [comment removed for export] *)

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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_aalloc2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aunwind.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc__A3W.F_aalloc.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_amalloc_iseg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc__A3W.F_amalloc_icpt.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_iseg__A3W.F_acalloc_iseg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_aalloc2g0.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3g0__A3W.F_aalloc3g0.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_aalloc2g.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3g.TwB.
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
(* [comment removed for export] *)
Local Ltac hide_disj_all := repeat match goal with H : (_ \/ _) |- _ => change (?P) with (sf_hide P) in H end.
Local Ltac hide_disj_but X :=
  repeat match goal with H : (_ \/ _) |- _ => tryif constr_eq H X then fail else change (?P) with (sf_hide P) in H end.
Local Ltac lia_rel := first [ solve [ hide_disj_all; lia ] | match goal with X : (_ \/ _) |- _ => solve [ hide_disj_but X; lia ] end ].
(* [comment removed for export] *)
From Ltac2 Require Import Ltac2.
Local Ltac2 rlx_prune (x : ident) : unit :=
  let hs := Control.hyps () in
  let cs := zt_plain_consts () in
  let ids := List.map_filter (fun h => let (id, body, ty) := h in
                match body with
                | Some _ => None
                | None => if Ident.equal id x then None else if zt_plain_arith_s cs ty then None
                          else if zt_is_local id then zt_is_prop_some ty id else None
                end) hs in
  match ids with [] => () | _ :: _ => Std.clear ids end.
Local Ltac2 rlx_id (v : Ltac1.t) : ident :=
  match Ltac1.to_ident v with
  | Some id => id
  | None => match Constr.Unsafe.kind (Option.get (Ltac1.to_constr v)) with Constr.Unsafe.Var id => id | _ => Control.throw (Tactic_failure None) end
  end.
Set Default Proof Mode "Classic".
Local Ltac rlx_prune X := let f := ltac2:(x |- rlx_prune (rlx_id x)) in f X.
Local Ltac rlx_lia X := rlx_prune X; first [ zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac lia_rel ::= first [ solve [ hide_disj_all; lia ] | match goal with X : (_ \/ _) |- _ => solve [ hide_disj_but X; rlx_lia X ] end ].
Local Ltac lia_relc := repeat split; first [ lia_rel | lia ].
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
Local Ltac fp_cheap8 := first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs end | clear ]; Stdlib.micromega.Lia.lia.   (* [comment removed for export] *)
Local Ltac fp_find8c := first [ apply Exists_cons_hd; cbn [fst snd]; split; fp_cheap8 | apply Exists_cons_tl; fp_find8c ].
Local Ltac fp_find8 := first [ apply Exists_cons_hd; cbn [fst snd]; split; lia | apply Exists_cons_tl; fp_find8 ].
Local Ltac fp_cover8 := apply sub_fp_cover8; repeat (apply Forall_cons; [ cbn [fst snd]; first [left; fp_cheap8 | right; fp_find8c | right; fp_find8] | ]); apply Forall_nil.
(* [comment removed for export] *)
Local Ltac transport_call_munch_tac ::= first [ fp_cover8 | unfold sub_fp; cbn [outside]; first [ match goal with Hs : bv_unsigned _ = bv_unsigned _ + _ |- _ => clear -Hs; intros; lia end | clear; intros; lia | intros; slia ] ].
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
(* [comment removed for export] *)
#[using="Type"] Local Lemma ablk_int : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6307840 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
#[using="Type"] Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
#[using="Type"] Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6307840 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
(* [comment removed for export] *)
#[using="Type"] Local Lemma ablk_shad_int : forall a ms, ablk a (a + ms) -> a mod 8 = 0 -> 0 <= ms ->
  exists k, 0 <= k <= 1 /\ a + ms <= shad a + k * 18446744073709551616 /\ shad a + ms / 8 + 8 <= a + (1 - k) * 18446744073709551616
            /\ 2148239360 <= shad a /\ shad a + ms / 8 <= 17594333495296.
Proof.
  intros a ms H A8 M0. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. rewrite !Shadow.shad_div. unfold AsanEmbed.ASHOFF.
  destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; Z.div_mod_to_equations; lia.
Qed.
Section WithDepot.
Variable DI : ADepotIface.

Notation malloc_W L sp t c AB UB PG pgw n :=
  ([(bv_unsigned sp - 4096, bv_unsigned sp); (t + 208 + c * 80, t + 208 + c * 80 + 4); (t + 2784, t + 2792);
    (t + 2800, t + 3168); (t + 3168, t + 3169); (UB - 16, UB + n); (AB, AB + 16);
    (shad UB, shad UB + shlen (n - n mod 8)); (PG, PG + pgw);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z) (only parsing).

(* [comment removed for export] *)
Definition malloc_post_genU (L : alayout) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (n t c cnt AB UB PG pgw lo b1 : Z) (maxc csz : word) (ub : list byte) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (id : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (sj' : list word) (stj' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 UB) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (malloc_W L sp t c AB UB PG pgw n) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ 0 < id < 2^31
    /\ rw_cells asegs m' (t + 208 + c * 80) [C4 (Z_to_bv 64 (cnt - 1)); C4 maxc; C8 csz]
    /\ rw_cells asegs m' (t + 2784) [C8 stj']
    /\ u64arr asegs m' (t + 2800) sj' /\ length sj' = 46%nat
    /\ rw_cells asegs m' (t + 3168) [C1 (Z_to_bv 8 0)]
    /\ rw_cells asegs m' (UB + -16) [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 (Z.lor (Z.land (hdr_b1_mid b1) 243) 0)); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)]
    /\ rw_cells asegs m' UB [CB (Z.to_nat n) ub]
    /\ (16 < rz_size n -> rw_cells asegs m' AB [C8 (Z_to_bv 64 0xCC6E96B9CC6E96B9); C8 (Z_to_bv 64 (UB + -16))])
    /\ rw_cells asegs m' (shad UB) [CB (Z.to_nat (shlen (n - n mod 8))) (repeat (Z_to_bv 8 0) (Z.to_nat (shlen (n - n mod 8))))]
    /\ (n mod 8 <> 0 -> rw_cells asegs m' PG [C1 (Z_to_bv 8 (n mod 8))])
    /\ ADEPOT DI L m'.

Definition calloc_tail_gen__stmt : Prop := forall (L : alayout) RNG (ra sp gp tp spA : word) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s4A s5A s6A s3i s2i s1i s0i : word)
    (F : bvmap 5 word) fc (m : amem)
    (n t c cnt AB UB PG pgw lo b0 b1 szh szl ctxj sz SB : Z) (maxc csz stj j1 j2 : word) (pj : byte)
    (sj : list word) (sjunk uj fr0 frc junk0 junk2 : list byte) (tb : list word) (tr : list Z),
  let ctx := al_ctx L in
  bv_unsigned spA = bv_unsigned sp - 2192 ->
  stk asegs m lo (bv_unsigned sp - 2320) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  1 <= n -> is_primary n = true ->
  (* [comment removed for export] *)
  allocA_cells m ctx t -> poison_cells m ->
  rw_cells asegs m 0xac24d [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m 0xac224 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->
  rw_cells asegs m 0xa64e8 [C8 (Z_to_bv 64 0x10)] -> rw_cells asegs m (ATPv + 16) [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m 0x1404c0 [C8 (Z_to_bv 64 0)] ->
  (* [comment removed for export] *)
  rw_cells asegs m (ctx + 8) [C4 (Z_to_bv 64 0)] -> rw_cells asegs m t [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> sclr ctx 65536 ->
  iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> t mod 4096 = 0 -> sclr t 4096 ->
  (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  (* [comment removed for export] *)
  class_id (needed_size n) = c ->
  rw_cells asegs m (t + 208 + c * 80) [C4 (Z_to_bv 64 (cnt - 1)); C4 maxc; C8 csz] ->
  rw_cells asegs m (t + 2784) [C8 stj] ->
  (* [comment removed for export] *)
  UB = AB + rz_size n -> 0x10007fff8000 <= AB -> UB + (size_of_class (class_id (needed_size n)) - rz_size n) <= ATOP -> AB mod 16 = 0 ->
  needed_size n <= size_of_class (class_id (needed_size n)) <= 65536 ->
  PG = shad UB + shlen (n - n mod 8) -> pgw = (if n mod 8 =? 0 then 0 else 1) ->
  0x2008fff7000 <= shad AB -> shad AB + 2 <= shad UB -> 0 <= shlen (n - n mod 8) <= 8192 -> PG + 1 <= 0x10007fff8000 ->
  rw_cells asegs m (UB + -16) [C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 szh); C4 (Z_to_bv 64 szl); C8 (Z_to_bv 64 ctxj)] ->
  0 <= b1 < 256 ->
  rw_cells asegs m UB [CB (Z.to_nat n) uj] ->
  (16 < rz_size n -> rw_cells asegs m AB [C8 j1; C8 j2]) ->
  rw_cells asegs m (shad AB) [C1 (Z_to_bv 8 0xfa)] ->
  rw_cells asegs m (shad UB) [CB (Z.to_nat (shlen (n - n mod 8))) sjunk] ->
  (n mod 8 <> 0 -> rw_cells asegs m PG [C1 pj]) ->
  (* [comment removed for export] *)
  (t + 4096 <= AB \/ AB + 65536 <= t) -> (ctx + 4096 <= AB \/ AB + 65536 <= ctx) ->
  (al_nodes L + 1048576 <= AB \/ AB + 65536 <= al_nodes L) -> (al_store L + 8388608 <= AB \/ AB + 65536 <= al_store L) -> tclr AB 65536 ->
  (t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) -> (t + 4096 <= al_store L \/ al_store L + 8388608 <= t) ->
  (ctx + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= ctx) -> (ctx + 4096 <= al_store L \/ al_store L + 8388608 <= ctx) -> tclr (al_nodes L) 1048576 -> tclr (al_store L) 8388608 ->
  sclr (al_nodes L) 1048576 -> al_nodes L + 1048576 <= ATOP -> sclr (al_store L) 8388608 -> al_store L + 8388608 <= ATOP ->
  (* [comment removed for export] *)
  rw_cells asegs m (bv_unsigned sp - 2320)
     [CB 8 fr0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 16); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6A; C8 s5A;
      C8 s4A; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 AINSTANCE); C8 (Z_to_bv 64 (bv_unsigned sp + -2136)); C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 0x3464c)] ->
  rw_cells asegs m (bv_unsigned sp + -2192) [CB 8 frc; C8 s3i; C8 s2i; C8 s1i; C8 s0i; C8 (Z_to_bv 64 0x56728)] ->
  rw_cells asegs m (bv_unsigned sp + -2144) [CB 8 junk0] ->
  (* [comment removed for export] *)
  rw_cells asegs m (AINSTANCE + 32) [C8 (Z_to_bv 64 SB)] -> 0 <= SB -> SB <= UB -> UB < SB + 137438953472 -> SB + 137438953472 < 2^64 ->
  rw_cells asegs m (bv_unsigned sp + -2136) [C8 (Z_to_bv 64 (bv_unsigned sp + -2136 + 16)); C8 (Z_to_bv 64 sz)] ->
  sz = 1 + Z.of_nat (length tr) -> sz <= 255 ->
  u64arr asegs m (bv_unsigned sp + -2136 + 16) tb -> length tb = 255%nat ->
  map bv_unsigned (firstn (Datatypes.S (length tr)) tb) = ACALLOC_PC :: tr ->
  In (ACALLOC_PC :: tr) (al_U L) -> bv_unsigned sp < 2^47 ->
  rw_cells asegs m (bv_unsigned sp + -80) [C8 sp; CB 8 junk2; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ADEPOT DI L m ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 ->
  rng RNG (UB - 16) (n + 16) -> rng RNG AB 16 -> rng RNG (shad AB) 1 -> rng RNG (shad UB) (shlen (n - n mod 8)) -> (n mod 8 <> 0 -> rng RNG PG 1) ->
  AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L ->      (* [comment removed for export] *)
  evtF asegs RNG (malloc_post_genU L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n t c cnt AB UB PG pgw lo b1 maxc csz (repeat (Z_to_bv 8 0) (Z.to_nat n)) m)
    (MS (mkR (Z_to_bv 64 0x33f10) (Z_to_bv 64 (bv_unsigned spA + -128)) gp tp t0 t1 t2
             (Z_to_bv 64 1) (Z_to_bv 64 n) (Z_to_bv 64 AB) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 8) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n)
             (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 t) (Z_to_bv 64 1)
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x33f10) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 5).
Variable spA : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 6).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 7).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 8).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 9).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 10).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 11).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 12).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 13).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 14).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 15).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 16).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 17).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 18).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 19).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 20).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 21).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 22).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 23).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 24).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 25).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 26).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 27).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 28).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 29).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 30).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 31).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 32).
Variable s4A : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 33).
Variable s5A : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 34).
Variable s6A : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 35).
Variable s3i : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 36).
Variable s2i : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 37).
Variable s1i : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 38).
Variable s0i : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 39).
Variable F : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 40).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 41).
Variable m : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 42).
Variable n : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 43).
Variable t : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 44).
Variable c : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 45).
Variable cnt : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 46).
Variable AB : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 47).
Variable UB : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 48).
Variable PG : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 49).
Variable pgw : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 50).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 51).
Variable b0 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 52).
Variable b1 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 53).
Variable szh : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 54).
Variable szl : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 55).
Variable ctxj : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 56).
Variable sz : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 57).
Variable SB : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 58).
Variable maxc : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 59).
Variable csz : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 60).
Variable stj : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 61).
Variable j1 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 62).
Variable j2 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 63).
Variable pj : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 64).
Variable sj : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 65).
Variable sjunk : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 66).
Variable uj : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 67).
Variable fr0 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 68).
Variable frc : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 69).
Variable junk0 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 70).
Variable junk2 : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 71).
Variable tb : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 72).
Variable tr : ltac2:(SecDietF.SzSecF.ty 'calloc_tail_gen__stmt 73).
#[using="Type"] Lemma calloc_tail_gen__body : ltac:(let T := type of (fun (h : calloc_tail_gen__stmt) => h L RNG ra sp gp tp spA t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s4A s5A s6A s3i s2i s1i s0i F fc m n t c cnt AB UB PG pgw lo b0 b1 szh szl ctxj sz SB maxc csz stj j1 j2 pj sj sjunk uj fr0 frc junk0 junk2 tb tr) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (ra, (sp, (gp, (tp, (spA, (t0, (t1, (t2, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (t3, (t4, (t5, (t6, (s0, (s1, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (s4A, (s5A, (s6A, (s3i, (s2i, (s1i, (s0i, (F, (fc, (m, (n, (t, (c, (cnt, (AB, (UB, (PG, (pgw, (lo, (b0, (b1, (szh, (szl, (ctxj, (sz, (SB, (maxc, (csz, (stj, (j1, (j2, (pj, (sj, (sjunk, (uj, (fr0, (frc, (junk0, (junk2, (tb, tr)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) as _.
 cbv zeta.
  intros HspA ST CEIL LO MI TP N PRIM AC PC PP FLG HK MCS CF34 CX8 TT0 UW STATS LSJ CX0 CX1 CXS T0 T1 TAL TS CT2
         HC CRa STSa HUB ABLO UBHI AB16 NSZ HPG HPW SB1 SB2 SB3 SB4 HDR B1 UJ LH SHA SHU SHP
         DJT DJC DJN DJS XTAB DTN DTS DCN DCS XTNO XTST N0 N1 R0 R1 FRa FR16 FRP INST PSB0 PSB1 PSB2 PSB3 SS SZ SZB TB LTB TRF TRU S47 FRS DEP
         RIMG RTLS RSTK RCTX RT RNO RST RU RAB RSA RSU RSP NI SI. band_lin.   (* [comment removed for export] *)
  unfold AIMG_HI in CX0, NI, SI.
  (nd_pre (sclr_int _ _ TS ltac:(clear -T0; lia) ltac:(clear -T1; lia)) 4%nat; intros kT TBND TBNDa TBNDb; nd_post).   (* [comment removed for export] *)
  (nd_pre (sclr_int _ _ CXS ltac:(clear -CX0; lia) ltac:(clear -CX1; lia)) 4%nat; intros kC CBND CBNDa CBNDb; nd_post).
  (nd_pre (sclr_int _ _ N0 ltac:(clear -NI; lia) ltac:(clear -N1; lia)) 4%nat; intros kN NBND NBNDa NBNDb; nd_post).
  (nd_pre (sclr_int _ _ R0 ltac:(clear -SI; lia) ltac:(clear -R1; lia)) 4%nat; intros kR SBND SBNDa SBNDb; nd_post).
  assert (PW01 : 0 <= pgw <= 1) by (rewrite HPW; destruct (n mod 8 =? 0); lia).
  (pose proof (prim_facts n N PRIM) as ndP__; nd_pre ndP__ 8%nat; intros NS RZR RZE RZM RLR RSR RSM NSR; nd_post).
  (pose proof (prim_class_facts n c N PRIM HC) as ndP__; nd_pre ndP__ 5%nat; intros C16 NSZ2 SM16 SMALL MC2; nd_post).
  (* [comment removed for export] *)
  destruct (tclr_int_lem _ _ XTAB ltac:(clear -ABLO; lia) ltac:(clear -UBHI HUB NSZ NS RZR RSR; pose proof atop_range; lia)) as (kLA & LABND).
  destruct (tclr_int_lem _ _ XTNO ltac:(clear -NI; lia) ltac:(clear -N1; pose proof atop_range; lia)) as (kLN & LNBND).
  destruct (tclr_int_lem _ _ XTST ltac:(clear -SI; lia) ltac:(clear -R1; pose proof atop_range; lia)) as (kLS & LSBND).
  pose proof AC as AC'. (nd_pre AC' 8%nat; intros INI RSS IMAX TI TK T88 TSD CT; nd_post).
  unfold AIMG_HI, AINSTANCE, ATP88, ATSD, ATSDI, ATSDK, AINITED, ARSSLIM, ACALLOC_PC in *. change (701336 + 32) with 701368 in INST.
  word_range sp SPR.
  box DJT. box DJC. box DJN. box DJS. box DTN. box DTS. box DCN. box DCS. box CT2.
  (* [comment removed for export] *)
  replace (bv_unsigned sp - 2320) with (bv_unsigned spA + -128) in ST, FRa by lia.
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (allocBC_gen0 DI L RNG spA gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m n (bv_unsigned sp + -2136) t AB UB PG pgw lo b0 b1 szh szl ctxj sz 353976 pj sjunk tb tr fr0 _ _ _ _ _ _ _ _ _ _ _ _ _).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact ST
         | |- mem_inv _ _ => exact MI
         | |- poison_cells _ => exact PC
         | |- ADEPOT _ _ _ => exact DEP
         | |- @eq word _ _ => first [reflexivity | exact TP]
         | |- u64arr _ _ _ _ => exact TB
         | |- _ \/ _ => first [unboxed DJT | unboxed DJC | unboxed DJN | unboxed DJS]
         | |- rng _ _ _ => solve_rng
         | |- ~ _ -> _ => exact SHP
         | |- _ -> rw_cells _ _ _ _ => exact LH
         end.
    all: try eassumption. all: try (unfold AIMG_HI; lia).
    all: match goal with |- ?G => idtac "REMBC" G end. }
  cbv beta. intros ms2 PB. unfold allocBC_postG in PB.
  (nd_pre PB 20%nat; intros id raB t0b t1b t2b a0b a1b a2b a3b a4b a5b a6b a7b s6b t3b t4b t5b t6b m2 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 9%nat; intros MUb WMb MIb STb IDR HDRb SHUb SHPb DEPb; nd_post).
  rewrite ?HspA in MUb.
  (* [comment removed for export] *)
  xport FRP MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia). xport INST MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia).
  xport FRa MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia).
  xport STATS MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; ub DTN; ub DTS; lia_relc).   (* [comment removed for export] *)
  xport TI MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia). xport TK MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia). xport T88 MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia). xport TSD MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia).
  xport CT MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJC; ub DCN; ub DCS; lia_relc).
  xport FLG MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia). xport HK MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia). xport MCS MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia). xport CF34 MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia).
  pose proof PC as PC'. (nd_pre PC' 7%nat; intros GOT GOT80 REAL PC4 PC5 PC6 PC7; nd_post).
  xport GOT MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia). xport GOT80 MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia). xport REAL MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia).
  xport PC4 MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia). xport PC5 MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia).
  xport UJ MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJN; ub DJS; lia_relc).
  xport CRa MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; ub DTN; ub DTS; lia_relc). xport STSa MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; ub DTN; ub DTS; lia_relc).
  xport UW MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; ub DTN; ub DTS; lia_relc).
  xport FR16 MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia). xport SS MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia). xport FRS MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia).
  xport TB MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; rewrite LTB; lia).
  assert (LH2 : 16 < rz_size n -> rw_cells asegs m2 AB [C8 j1; C8 j2]).
  { intros RZ. specialize (LH RZ). pose proof (rz_size_cases n) as RZC.
    xport LH MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS RZ RZC; ub DJN; ub DJS; lia_relc). exact LH. }
  clear LH SHP.
  pose proof (hdr_b1_mid_range b1 ltac:(lia)) as B1M.
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (allocD_gen0 L RNG spA gp tp F fc m2 n t c AB UB lo b0 (hdr_b1_mid b1) id (bv_unsigned sp + -2136) sj uj j1 j2 fr0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact STb
         | |- mem_inv _ _ => exact MIb
         | |- @eq word _ _ => first [reflexivity | exact TP]
         | |- u64arr _ _ _ _ => exact STATS
         | |- _ \/ _ => first [unboxed DJT | unboxed DJC | unboxed DJN | unboxed DJS]
         | |- rng _ _ _ => solve_rng
         | |- _ -> rw_cells _ _ _ _ => exact LH2
         | |- rw_cells _ _ (_ + 152) _ => exact CT
         | |- rw_cells _ _ (_ + -16) _ => exact HDRb
         | |- tclr _ _ => apply (tclr_sub AB 65536); [exact XTAB | clear; lia | clear -HUB NSZ NS RZR RSR N; lia]      (* [comment removed for export] *)
         end.
    all: try eassumption. all: try (unfold AIMG_HI; lia).
    all: match goal with |- ?G => idtac "REMD" G end. }
  cbv beta. intros ms3 PD. unfold allocD_postG0 in PD.
  (nd_pre PD 17%nat; intros t0d t1d t2d a1d a2d a3d a4d a5d a6d a7d t3d t4d t5d t6d m3 sj3 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 9%nat; intros MUd WMd MId STd STATSd LSJd UFd HDRd LHd; nd_post).
  rewrite ?HspA in MUd.
  xport CRa MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; ylia). xport STSa MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; ylia).
  xport SHUb MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia). xport UW MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; ylia).   (* [comment removed for export] *)
  xport FRP MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia). xport INST MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia). xport GOT80 MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia). xport REAL MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia).
  xport FR16 MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia). xport SS MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia). xport FRS MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia). xport TB MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; rewrite LTB; lia).
  assert (SHPd : n mod 8 <> 0 -> rw_cells asegs m3 PG [C1 (Z_to_bv 8 (n mod 8))]).
  { intros NE. specialize (SHPb NE). xport SHPb MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS NE; lia). exact SHPb. }
  assert (LH4 : 16 < rz_size n -> rw_cells asegs m3 AB [C8 (Z_to_bv 64 0xCC6E96B9CC6E96B9); C8 (Z_to_bv 64 (UB + -16))]).
  { intros RZ. exact (LHd RZ). }
  assert (DEPd : ADEPOT DI L m3).
  { eapply (adi_frame DI); [exact DEPb | exact MUd | exact WMd |].
    repeat (apply Forall_cons; [cbn [fst snd]; intros a Ha; first [clear -Ha HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RSR NSR HPG PW01 SB1 SB2 SB3 SB4 C16 LSJ N DTN DTS DJN DJS; ub DTN; ub DTS; ub DJN; ub DJS; ylia | ub DTN; ub DTS; ub DJN; ub DJS; ylia]|]). apply Forall_nil. }   (* [comment removed for export] *)
  (* [comment removed for export] *)
  replace (ret_pc (Z_to_bv 64 0x3464c)) with (Z_to_bv 64 0x3464c) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  assert (EspA : spA = Z_to_bv 64 (bv_unsigned sp + -2192)).
  { enough (E : Z_to_bv 64 (bv_unsigned spA) = Z_to_bv 64 (bv_unsigned sp + -2192)) by (rewrite Z_to_bv_bv_unsigned in E; exact E).
    apply Z_to_bv_eqm. rewrite HspA. zeq. }
  rewrite EspA. rewrite HspA in STd. replace (bv_unsigned sp - 2192) with (bv_unsigned sp + -2192) in STd by lia.
  apply rw_cells_of_u64arr in TB. rewrite LTB in TB.
  eapply evtF_cut.
  { eapply (cicptC_spec RNG sp gp tp) with (SB := SB) (n := n) (uj := uj);
      [exact STd | atop_facts; lia | lia | exact MId | clear -ABLO HUB RZR; lia | exact N | clear -UBHI CEIL HUB NSZ NS RZR RSR N; atop_facts; lia
      | exact PSB0 | exact PSB1 | exact PSB2 | exact PSB3 | exact INST | exact GOT80 | exact REAL | exact UFd | exact FR16
      | eexists; split; [exact FRP | reflexivity]
      | eexists; split; [exact SS | reflexivity]
      | eexists; split; [replace (bv_unsigned sp + -2120) with (bv_unsigned sp + -2136 + 16) by lia; exact TB | reflexivity]
      | exact FRS | exact RIMG | exact RTLS | solve_rng | eapply rng_sub'; [exact RU | clear -N; lia] ]. }
  cbv beta. intros ms5 PCC. unfold cicptC_post in PCC.
  (nd_pre PCC 16%nat; intros t0e t1e t2e a1e a2e a3e a4e a5e a6e a7e t3e t4e t5e t6e m5 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 5%nat; intros MUc WMc MIc STc UZ; nd_post).
  apply evtF_done.
  (* [comment removed for export] *)
  xport CRa MUc WMc ltac:(first [clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT; ub DJT; ylia | ub DJT; ylia]). xport STSa MUc WMc ltac:(first [clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT; ub DJT; ylia | ub DJT; ylia]). xport STATSd MUc WMc ltac:(rewrite ?upd_length; first [clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT; ub DJT; ylia | ub DJT; ylia]).
  xport HDRd MUc WMc ltac:(first [clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT; ub DJT; ylia | ub DJT; ylia]). clear UFd. xport SHUb MUc WMc ltac:(first [clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT; ub DJT; ylia | ub DJT; ylia]). xport UW MUc WMc ltac:(first [clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT; ub DJT; ylia | ub DJT; ylia]).
  assert (LH5 : 16 < rz_size n -> rw_cells asegs m5 AB [C8 (Z_to_bv 64 0xCC6E96B9CC6E96B9); C8 (Z_to_bv 64 (UB + -16))]).
  { intros RZ. specialize (LH4 RZ). pose proof (rz_size_cases n) as RZC. xport LH4 MUc WMc ltac:(first [clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT RZC; ub DJT; ylia | ub DJT; ylia]). exact LH4. }
  assert (SHP5 : n mod 8 <> 0 -> rw_cells asegs m5 PG [C1 (Z_to_bv 8 (n mod 8))]).
  { intros NE. specialize (SHPd NE). xport SHPd MUc WMc ltac:(first [clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT; ub DJT; ylia | ub DJT; ylia]). exact SHPd. }
  assert (DEP5 : ADEPOT DI L m5).
  { eapply (adi_frame DI); [exact DEPd | exact MUc | exact WMc |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; first [clear -Ha HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RSR NSR HPG PW01 SB1 SB2 SB3 SB4 C16 LSJ N DTN DTS DJN DJS; ub DTN; ub DTS; ub DJN; ub DJS; ylia | ub DTN; ub DTS; ub DJN; ub DJS; ylia] | apply Forall_nil]. }
  assert (MU : munch (malloc_W L sp t c AB UB PG pgw n) m m5).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUc]].
    eapply munch_trans; [| eapply munch_weaken; [| exact MUd]].
    eapply munch_weaken; [| exact MUb].
    all: first [clear -N C16 PW01 HspA; unfold sub_fp; cbn [outside]; intros q Hq; lia | fp_cover8 | unfold sub_fp; cbn [outside]; intros q Hq; lia]. }   (* [comment removed for export] *)
  assert (WM : wmono asegs m m5).
  { eapply wmono_trans; [exact WMb|]. eapply wmono_trans; [exact WMd| exact WMc]. }
  unfold malloc_post_genU. exists id. do 14 eexists. exists m5, sj3, stj. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MIc|]. split; [exact STc|]. split; [exact IDR|].
  split; [exact CRa|]. split; [exact STSa|]. split; [exact STATSd|]. split; [exact LSJd|]. split; [exact UW|].
  split; [exact HDRd|]. split; [exact UZ|]. split; [exact LH5|]. split; [exact SHUb|]. split; [exact SHP5|]. exact DEP5.
  Unshelve. all: try exact STb; try exact ST.
Qed.
End Zd1.
#[using="Type"] Lemma calloc_tail_gen : ltac:(let t := eval cbv delta [calloc_tail_gen__stmt] in calloc_tail_gen__stmt in exact t).
Proof. exact calloc_tail_gen__body. Qed.
End WithDepot.
End CANSEC1.
(* [comment removed for export] *)
End TwB.
