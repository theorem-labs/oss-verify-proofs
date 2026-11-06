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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_memsetZ F_aunwind.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3 F_acache3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecSlog__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require NDestr.
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3g.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecFacts.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_agbb__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_s__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_adrain__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_memcpy.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc1b__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_acalloc_iseg__A3W.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_aalloc3g0.
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import F_aalloc3g.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
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
Definition allocD_postG0 (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32)
    (n t AB UB lo b1m id : Z) (ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word) (uj : list byte) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' sj',
    ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 UB) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6)
             F (ret_pc ra0) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp + -128 - 32, bv_unsigned sp + -128); (t + 2800, t + 3168); (UB - 16, UB + n); (AB, AB + 16)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ u64arr asegs m' (t + 2800) sj' /\ length sj' = 46%nat
    /\ rw_cells asegs m' UB [CB (Z.to_nat n) uj]      (* [comment removed for export] *)
    /\ rw_cells asegs m' (UB + -16) [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 (Z.lor (Z.land b1m 243) 0)); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)]
    /\ (16 < rz_size n -> rw_cells asegs m' AB [C8 (Z_to_bv 64 0xCC6E96B9CC6E96B9); C8 (Z_to_bv 64 (UB + -16))]).

Definition allocD_gen0__stmt : Prop := forall (L : alayout) RNG sp gp tp (F : bvmap 5 word) fc (m : amem)
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
     [CB 8 fr0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 16); C8 s11v; C8 s10v; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v;
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
  evtF asegs RNG (allocD_postG0 sp gp tp F fc n t AB UB lo b1m id ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v uj m)
    (MS (mkR raX (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2
              (Z_to_bv 64 1) (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7
              (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 UB) (Z_to_bv 64 (UB + -16)) s6x
              (Z_to_bv 64 S) (Z_to_bv 64 0) (Z_to_bv 64 (UB + n)) (Z_to_bv 64 t) (Z_to_bv 64 1)
              t3 t4 t5 t6)
        F (Z_to_bv 64 0x34154) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 1).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 2).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 3).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 4).
Variable F : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 5).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 6).
Variable m : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 7).
Variable n : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 8).
Variable t : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 9).
Variable c : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 10).
Variable AB : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 11).
Variable UB : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 12).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 13).
Variable b0 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 14).
Variable b1m : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 15).
Variable id : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 16).
Variable S : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 17).
Variable sj : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 18).
Variable uj : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 19).
Variable j1 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 20).
Variable j2 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 21).
Variable fr0 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 22).
Variable raX : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 23).
Variable ra0 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 24).
Variable s0v : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 25).
Variable s1v : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 26).
Variable s2v : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 27).
Variable s3v : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 28).
Variable s4v : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 29).
Variable s5v : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 30).
Variable s6v : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 31).
Variable s7v : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 32).
Variable s8v : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 33).
Variable s9v : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 34).
Variable s10v : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 35).
Variable s11v : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 36).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 37).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 38).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 39).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 40).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 41).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 42).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 43).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 44).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 45).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 46).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 47).
Variable s6x : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 48).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 49).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 50).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 51).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 52).
#[using="Type"] Lemma allocD_gen0__body : ltac:(let T := type of (fun (h : allocD_gen0__stmt) => h L RNG sp gp tp F fc m n t c AB UB lo b0 b1m id S sj uj j1 j2 fr0 raX ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6x t3 t4 t5 t6) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
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
  rename UJ into UF.
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
#[using="Type"] Lemma allocD_gen0 : ltac:(let t := eval cbv delta [allocD_gen0__stmt] in allocD_gen0__stmt in exact t).
Proof. exact allocD_gen0__body. Qed.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3g.TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
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
Definition allocD_postG0 (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32)
    (n t AB UB lo b1m id : Z) (ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word) (uj : list byte) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' sj',
    ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 UB) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6)
             F (ret_pc ra0) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp + -128 - 32, bv_unsigned sp + -128); (t + 2800, t + 3168); (UB - 16, UB + n); (AB, AB + 16)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ u64arr asegs m' (t + 2800) sj' /\ length sj' = 46%nat
    /\ rw_cells asegs m' UB [CB (Z.to_nat n) uj]      (* [comment removed for export] *)
    /\ rw_cells asegs m' (UB + -16) [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 (Z.lor (Z.land b1m 243) 0)); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)]
    /\ (16 < rz_size n -> rw_cells asegs m' AB [C8 (Z_to_bv 64 0xCC6E96B9CC6E96B9); C8 (Z_to_bv 64 (UB + -16))]).

Definition allocD_gen0__stmt : Prop := forall (L : alayout) RNG sp gp tp (F : bvmap 5 word) fc (m : amem)
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
     [CB 8 fr0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 16); C8 s11v; C8 s10v; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v;
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
  evtF asegs RNG (allocD_postG0 sp gp tp F fc n t AB UB lo b1m id ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v uj m)
    (MS (mkR raX (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2
              (Z_to_bv 64 1) (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7
              (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 UB) (Z_to_bv 64 (UB + -16)) s6x
              (Z_to_bv 64 S) (Z_to_bv 64 0) (Z_to_bv 64 (UB + n)) (Z_to_bv 64 t) (Z_to_bv 64 1)
              t3 t4 t5 t6)
        F (Z_to_bv 64 0x341bc) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 1).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 2).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 3).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 4).
Variable F : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 5).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 6).
Variable m : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 7).
Variable n : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 8).
Variable t : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 9).
Variable c : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 10).
Variable AB : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 11).
Variable UB : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 12).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 13).
Variable b0 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 14).
Variable b1m : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 15).
Variable id : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 16).
Variable S : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 17).
Variable sj : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 18).
Variable uj : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 19).
Variable j1 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 20).
Variable j2 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 21).
Variable fr0 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 22).
Variable raX : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 23).
Variable ra0 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 24).
Variable s0v : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 25).
Variable s1v : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 26).
Variable s2v : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 27).
Variable s3v : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 28).
Variable s4v : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 29).
Variable s5v : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 30).
Variable s6v : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 31).
Variable s7v : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 32).
Variable s8v : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 33).
Variable s9v : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 34).
Variable s10v : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 35).
Variable s11v : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 36).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 37).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 38).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 39).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 40).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 41).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 42).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 43).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 44).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 45).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 46).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 47).
Variable s6x : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 48).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 49).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 50).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 51).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen0__stmt 52).
#[using="Type"] Lemma allocD_gen0__body : ltac:(let T := type of (fun (h : allocD_gen0__stmt) => h L RNG sp gp tp F fc m n t c AB UB lo b0 b1m id S sj uj j1 j2 fr0 raX ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6x t3 t4 t5 t6) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
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
  rename UJ into UF.
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
#[using="Type"] Lemma allocD_gen0 : ltac:(let t := eval cbv delta [allocD_gen0__stmt] in allocD_gen0__stmt in exact t).
Proof. exact allocD_gen0__body. Qed.
End CANSEC2.
(* [comment removed for export] *)
End TwB.
End F_aalloc3g0.

(* [comment removed for export] *)
Module F_aalloc3s.
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecFacts F_memsetZ F_aunwind. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3 F_acache3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecSlog__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3g. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memsetZ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aunwind OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acache3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aclass2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3g.
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

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition allocD_sec__stmt : Prop := forall (L : alayout) RNG sp gp tp (F : bvmap 5 word) fc (m : amem)
    (n t AB UB lo b0 b1m id S : Z) (sj : list word) (uj : list byte) (j1 j2 : word)
    (fr0 : list byte) (raX ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s0x s6x s9x t3 t4 t5 t6 : word),
  stk asegs m lo (bv_unsigned sp + -128) -> ATOP <= lo -> lo <= bv_unsigned sp + -128 - 32 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  1 <= n <= AREQMAX -> is_primary n = false ->
  UB = AB + rz_size n -> ablk AB (UB + n) -> UB + n <= ATOP -> AB mod 16 = 0 ->
  (t + 4096 <= AB \/ UB + n <= t) ->
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
              s0x (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7
              (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 UB) (Z_to_bv 64 (UB + -16)) s6x
              (Z_to_bv 64 S) (Z_to_bv 64 0) s9x (Z_to_bv 64 t) (Z_to_bv 64 1)
              t3 t4 t5 t6)
        F (Z_to_bv 64 0x34154) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 1).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 2).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 3).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 4).
Variable F : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 5).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 6).
Variable m : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 7).
Variable n : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 8).
Variable t : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 9).
Variable AB : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 10).
Variable UB : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 11).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 12).
Variable b0 : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 13).
Variable b1m : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 14).
Variable id : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 15).
Variable S : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 16).
Variable sj : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 17).
Variable uj : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 18).
Variable j1 : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 19).
Variable j2 : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 20).
Variable fr0 : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 21).
Variable raX : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 22).
Variable ra0 : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 23).
Variable s0v : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 24).
Variable s1v : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 25).
Variable s2v : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 26).
Variable s3v : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 27).
Variable s4v : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 28).
Variable s5v : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 29).
Variable s6v : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 30).
Variable s7v : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 31).
Variable s8v : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 32).
Variable s9v : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 33).
Variable s10v : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 34).
Variable s11v : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 35).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 36).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 37).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 38).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 39).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 40).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 41).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 42).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 43).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 44).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 45).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 46).
Variable s0x : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 47).
Variable s6x : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 48).
Variable s9x : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 49).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 50).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 51).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 52).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 53).
Let fl := Z.min n 4096.
#[using="fl"] Lemma allocD_sec__body : ltac:(let T := type of (fun (h : allocD_sec__stmt) => h L RNG sp gp tp F fc m n t AB UB lo b0 b1m id S sj uj j1 j2 fr0 raX ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s0x s6x s9x t3 t4 t5 t6) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (sp, (gp, (tp, (F, (fc, (m, (n, (t, (AB, (UB, (lo, (b0, (b1m, (id, (S, (sj, (uj, (j1, (j2, (fr0, (raX, (ra0, (s0v, (s1v, (s2v, (s3v, (s4v, (s5v, (s6v, (s7v, (s8v, (s9v, (s10v, (s11v, (t0, (t1, (t2, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s0x, (s6x, (s9x, (t3, (t4, (t5, t6)))))))))))))))))))))))))))))))))))))))))))))))))))))) as _.

  intros ST CEIL LO MI TP N PRIM HUB ABLO UBHI AB16 DJT FR STATS LSJ TI TK T88 TSD CT CX0 CX1 T0 T1 TCB
         FLG GOT GOT80 REAL LS1 LS2 HK UJ HDR B1M IDR LH RIMG RTLS RSTK RCTX RT RU RAB. band_lin.   (* [comment removed for export] *)
  (pose proof (ablk_lin _ _ ABLO) as ndP__; nd_pre ndP__ 4%nat; intros AL1 AL2 AL3 AL4; nd_post). unfold AIMG_HI in AL1. tclr_int TCB. fold AIMG_HI in AL1.   (* [comment removed for export] *)
  unfold AIMG_HI, ATP88, ATSD, AREQMAX in *.
  (pose proof (sec_facts n ltac:(unfold AREQMAX; lia) PRIM) as ndP__; nd_pre ndP__ 10%nat; intros NB RZ2 RSE RSR RSM NSE MSE MSR MSM MSB; nd_post).
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp + -128 - 32, bv_unsigned sp + -128); (t + 2800, t + 3168); (UB - 16, UB + n); (AB, AB + 16)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  box DJT. box LH.
  snapshot [(bv_unsigned sp + -128 - 32, bv_unsigned sp + -128); (t + 2800, t + 3168)]%Z MUs WMs.
  box UJ. box HDR.
  step. call_sp (thread_stats_spec RNG (al_ctx L) t lo).
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- stk _ _ _ _ => eassumption
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
  step. if_cases K0; zify_cond K0. { exfalso. lia. }             (* [comment removed for export] *)
  aload STATS 13 (t + 2800 + 104).                               (* [comment removed for export] *)
  zstep.                                                         (* [comment removed for export] *)
  astore STATS 13.                                               (* [comment removed for export] *)
  step. step. if_lit.                                            (* [comment removed for export] *)
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
  step. step. lstep. step. if_lit.                               (* [comment removed for export] *)
  eapply evtF_cut; [eapply (fill_len_spec RNG); [lia | exact RIMG | exact RTLS] |]. cbv beta. intros msF ->.   (* [comment removed for export] *)
  chg (Z.min n 4096) fl.
  destruct (cb_take _ _ n fl uj UJ ltac:(subst fl; lia)) as [UJ1 UJ2]. clear UJ.
  step. step. step. lstep. step.                                 (* [comment removed for export] *)
  step. call (memset_specZ RNG UB 0xbe fl (firstn (Z.to_nat fl) uj)).
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- mem_inv _ _ => assumption
       | |- @eq word _ _ => reflexivity
       | |- rw_cells _ _ _ [CB _ _] => exact UJ1
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
  step. if_cases K3; zify_cond K3. { exfalso. clear -K3 RZ2 HUB; lia. }   (* [comment removed for export] *)
  - (* [comment removed for export] *)
    specialize (LH ltac:(rewrite RZ2; lia)).
    zstep. step. if_cases K4; zify_cond K4. { exfalso. clear -K4 RZ2 HUB; lia. }   (* [comment removed for export] *)
    step. step.                                                  (* [comment removed for export] *)
    step. step. step.                                            (* [comment removed for export] *)
    step. step. step. call_sp (run_malloc_hooks_spec RNG).
    all: try lazymatch goal with
         | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
         | |- stk _ _ _ _ => eassumption
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
#[using="Type"] Lemma allocD_sec : ltac:(let t := eval cbv delta [allocD_sec__stmt] in allocD_sec__stmt in exact t).
Proof. exact allocD_sec__body. Qed.
End CANSEC1.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memsetZ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aunwind.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acache3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aclass2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3g.TwB.
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

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition allocD_sec__stmt : Prop := forall (L : alayout) RNG sp gp tp (F : bvmap 5 word) fc (m : amem)
    (n t AB UB lo b0 b1m id S : Z) (sj : list word) (uj : list byte) (j1 j2 : word)
    (fr0 : list byte) (raX ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s0x s6x s9x t3 t4 t5 t6 : word),
  stk asegs m lo (bv_unsigned sp + -128) -> ATOP <= lo -> lo <= bv_unsigned sp + -128 - 32 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  1 <= n <= AREQMAX -> is_primary n = false ->
  UB = AB + rz_size n -> ablk AB (UB + n) -> UB + n <= ATOP -> AB mod 16 = 0 ->
  (t + 4096 <= AB \/ UB + n <= t) ->
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
              s0x (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7
              (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 UB) (Z_to_bv 64 (UB + -16)) s6x
              (Z_to_bv 64 S) (Z_to_bv 64 0) s9x (Z_to_bv 64 t) (Z_to_bv 64 1)
              t3 t4 t5 t6)
        F (Z_to_bv 64 0x341bc) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 1).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 2).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 3).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 4).
Variable F : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 5).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 6).
Variable m : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 7).
Variable n : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 8).
Variable t : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 9).
Variable AB : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 10).
Variable UB : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 11).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 12).
Variable b0 : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 13).
Variable b1m : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 14).
Variable id : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 15).
Variable S : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 16).
Variable sj : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 17).
Variable uj : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 18).
Variable j1 : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 19).
Variable j2 : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 20).
Variable fr0 : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 21).
Variable raX : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 22).
Variable ra0 : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 23).
Variable s0v : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 24).
Variable s1v : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 25).
Variable s2v : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 26).
Variable s3v : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 27).
Variable s4v : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 28).
Variable s5v : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 29).
Variable s6v : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 30).
Variable s7v : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 31).
Variable s8v : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 32).
Variable s9v : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 33).
Variable s10v : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 34).
Variable s11v : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 35).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 36).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 37).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 38).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 39).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 40).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 41).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 42).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 43).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 44).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 45).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 46).
Variable s0x : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 47).
Variable s6x : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 48).
Variable s9x : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 49).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 50).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 51).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 52).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'allocD_sec__stmt 53).
Let fl := Z.min n 4096.
#[using="fl"] Lemma allocD_sec__body : ltac:(let T := type of (fun (h : allocD_sec__stmt) => h L RNG sp gp tp F fc m n t AB UB lo b0 b1m id S sj uj j1 j2 fr0 raX ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s0x s6x s9x t3 t4 t5 t6) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (sp, (gp, (tp, (F, (fc, (m, (n, (t, (AB, (UB, (lo, (b0, (b1m, (id, (S, (sj, (uj, (j1, (j2, (fr0, (raX, (ra0, (s0v, (s1v, (s2v, (s3v, (s4v, (s5v, (s6v, (s7v, (s8v, (s9v, (s10v, (s11v, (t0, (t1, (t2, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s0x, (s6x, (s9x, (t3, (t4, (t5, t6)))))))))))))))))))))))))))))))))))))))))))))))))))))) as _.

  intros ST CEIL LO MI TP N PRIM HUB ABLO UBHI AB16 DJT FR STATS LSJ TI TK T88 TSD CT CX0 CX1 T0 T1 TCB
         FLG GOT GOT80 REAL LS1 LS2 HK UJ HDR B1M IDR LH RIMG RTLS RSTK RCTX RT RU RAB. band_lin.   (* [comment removed for export] *)
  (pose proof (ablk_lin _ _ ABLO) as ndP__; nd_pre ndP__ 4%nat; intros AL1 AL2 AL3 AL4; nd_post). unfold AIMG_HI in AL1. tclr_int TCB. fold AIMG_HI in AL1.   (* [comment removed for export] *)
  unfold AIMG_HI, ATP88, ATSD, AREQMAX in *.
  (pose proof (sec_facts n ltac:(unfold AREQMAX; lia) PRIM) as ndP__; nd_pre ndP__ 10%nat; intros NB RZ2 RSE RSR RSM NSE MSE MSR MSM MSB; nd_post).
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp + -128 - 32, bv_unsigned sp + -128); (t + 2800, t + 3168); (UB - 16, UB + n); (AB, AB + 16)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  box DJT. box LH.
  snapshot [(bv_unsigned sp + -128 - 32, bv_unsigned sp + -128); (t + 2800, t + 3168)]%Z MUs WMs.
  box UJ. box HDR.
  step. call_sp (thread_stats_spec RNG (al_ctx L) t lo).
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- stk _ _ _ _ => eassumption
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
  step. if_cases K0; zify_cond K0. { exfalso. lia. }             (* [comment removed for export] *)
  aload STATS 13 (t + 2800 + 104).                               (* [comment removed for export] *)
  zstep.                                                         (* [comment removed for export] *)
  astore STATS 13.                                               (* [comment removed for export] *)
  step. step. if_lit.                                            (* [comment removed for export] *)
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
  step. step. lstep. step. if_lit.                               (* [comment removed for export] *)
  eapply evtF_cut; [eapply (fill_len_spec RNG); [lia | exact RIMG | exact RTLS] |]. cbv beta. intros msF ->.   (* [comment removed for export] *)
  chg (Z.min n 4096) fl.
  destruct (cb_take _ _ n fl uj UJ ltac:(subst fl; lia)) as [UJ1 UJ2]. clear UJ.
  step. step. step. lstep. step.                                 (* [comment removed for export] *)
  step. call (memset_specZ RNG UB 0xbe fl (firstn (Z.to_nat fl) uj)).
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- mem_inv _ _ => assumption
       | |- @eq word _ _ => reflexivity
       | |- rw_cells _ _ _ [CB _ _] => exact UJ1
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
  step. if_cases K3; zify_cond K3. { exfalso. clear -K3 RZ2 HUB; lia. }   (* [comment removed for export] *)
  - (* [comment removed for export] *)
    specialize (LH ltac:(rewrite RZ2; lia)).
    zstep. step. if_cases K4; zify_cond K4. { exfalso. clear -K4 RZ2 HUB; lia. }   (* [comment removed for export] *)
    step. step.                                                  (* [comment removed for export] *)
    step. step. step.                                            (* [comment removed for export] *)
    step. step. step. call_sp (run_malloc_hooks_spec RNG).
    all: try lazymatch goal with
         | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
         | |- stk _ _ _ _ => eassumption
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
#[using="Type"] Lemma allocD_sec : ltac:(let t := eval cbv delta [allocD_sec__stmt] in allocD_sec__stmt in exact t).
Proof. exact allocD_sec__body. Qed.
End CANSEC1.
(* [comment removed for export] *)
End TwB.
End F_aalloc3s.

(* [comment removed for export] *)
Module F_amalloc_tailg.
(* [comment removed for export] *)
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecSlog__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_agbb__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3 F_aunwind. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_s__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3g. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_aalloc2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aunwind OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc__A3W.F_aalloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_amalloc_iseg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc__A3W.F_amalloc_icpt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_aalloc2g OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3g.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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
Definition malloc_post_gen (L : alayout) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (n t c cnt AB UB PG pgw lo b1 : Z) (maxc csz : word) (uj : list byte) (m : amem) : machine_state -> Prop :=
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
    /\ rw_cells asegs m' UB [CB (Z.to_nat n) (repeat (Z_to_bv 8 0xbe) (Z.to_nat (Z.min n 4096)) ++ skipn (Z.to_nat (Z.min n 4096)) uj)]
    /\ (16 < rz_size n -> rw_cells asegs m' AB [C8 (Z_to_bv 64 0xCC6E96B9CC6E96B9); C8 (Z_to_bv 64 (UB + -16))])
    /\ rw_cells asegs m' (shad UB) [CB (Z.to_nat (shlen (n - n mod 8))) (repeat (Z_to_bv 8 0) (Z.to_nat (shlen (n - n mod 8))))]
    /\ (n mod 8 <> 0 -> rw_cells asegs m' PG [C1 (Z_to_bv 8 (n mod 8))])
    /\ ADEPOT DI L m'.

Definition malloc_tail_gen__stmt : Prop := forall (L : alayout) RNG (ra sp gp tp spA : word) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0A s1A s2A s3A s4A s5A s0i : word)
    (F : bvmap 5 word) fc (m : amem)
    (n t c cnt AB UB PG pgw lo b0 b1 szh szl ctxj sz : Z) (maxc csz stj j1 j2 : word) (pj : byte)
    (sj : list word) (sjunk uj fr0 junk2 : list byte) (tb : list word) (tr : list Z),
  let ctx := al_ctx L in
  bv_unsigned spA = bv_unsigned sp - 2144 ->
  stk asegs m lo (bv_unsigned sp - 2272) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
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
  rw_cells asegs m (bv_unsigned sp - 2272)
     [CB 8 fr0; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 16); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5A;
      C8 s4A; C8 s3A; C8 s2A; C8 s1A; C8 s0A; C8 (Z_to_bv 64 0x33bd8)] ->
  rw_cells asegs m (bv_unsigned sp + -2144) [C8 s0i; C8 (Z_to_bv 64 0x56488)] ->
  rw_cells asegs m (bv_unsigned sp + -2128) [C8 (Z_to_bv 64 (bv_unsigned sp + -2128 + 16)); C8 (Z_to_bv 64 sz)] ->
  sz = 1 + Z.of_nat (length tr) -> sz <= 255 ->
  u64arr asegs m (bv_unsigned sp + -2128 + 16) tb -> length tb = 255%nat ->
  map bv_unsigned (firstn (Datatypes.S (length tr)) tb) = AMALLOC_PC :: tr ->
  In (AMALLOC_PC :: tr) (al_U L) -> bv_unsigned sp < 2^47 ->
  rw_cells asegs m (bv_unsigned sp + -72) [C8 sp; CB 8 junk2; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ADEPOT DI L m ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 ->
  rng RNG (UB - 16) (n + 16) -> rng RNG AB 16 -> rng RNG (shad AB) 1 -> rng RNG (shad UB) (shlen (n - n mod 8)) -> (n mod 8 <> 0 -> rng RNG PG 1) ->
  AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L ->      (* [comment removed for export] *)
  evtF asegs RNG (malloc_post_gen L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n t c cnt AB UB PG pgw lo b1 maxc csz uj m)
    (MS (mkR (Z_to_bv 64 0x33ea8) (Z_to_bv 64 (bv_unsigned spA + -128)) gp tp t0 t1 t2
             (Z_to_bv 64 1) (Z_to_bv 64 n) (Z_to_bv 64 AB) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 8) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n)
             (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 t) (Z_to_bv 64 1)
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x33ea8) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 5).
Variable spA : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 6).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 7).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 8).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 9).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 10).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 11).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 12).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 13).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 14).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 15).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 16).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 17).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 18).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 19).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 20).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 21).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 22).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 23).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 24).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 25).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 26).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 27).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 28).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 29).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 30).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 31).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 32).
Variable s0A : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 33).
Variable s1A : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 34).
Variable s2A : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 35).
Variable s3A : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 36).
Variable s4A : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 37).
Variable s5A : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 38).
Variable s0i : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 39).
Variable F : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 40).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 41).
Variable m : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 42).
Variable n : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 43).
Variable t : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 44).
Variable c : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 45).
Variable cnt : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 46).
Variable AB : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 47).
Variable UB : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 48).
Variable PG : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 49).
Variable pgw : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 50).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 51).
Variable b0 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 52).
Variable b1 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 53).
Variable szh : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 54).
Variable szl : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 55).
Variable ctxj : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 56).
Variable sz : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 57).
Variable maxc : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 58).
Variable csz : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 59).
Variable stj : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 60).
Variable j1 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 61).
Variable j2 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 62).
Variable pj : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 63).
Variable sj : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 64).
Variable sjunk : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 65).
Variable uj : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 66).
Variable fr0 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 67).
Variable junk2 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 68).
Variable tb : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 69).
Variable tr : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 70).
#[using="Type"] Lemma malloc_tail_gen__body : ltac:(let T := type of (fun (h : malloc_tail_gen__stmt) => h L RNG ra sp gp tp spA t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0A s1A s2A s3A s4A s5A s0i F fc m n t c cnt AB UB PG pgw lo b0 b1 szh szl ctxj sz maxc csz stj j1 j2 pj sj sjunk uj fr0 junk2 tb tr) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (ra, (sp, (gp, (tp, (spA, (t0, (t1, (t2, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (t3, (t4, (t5, (t6, (s0, (s1, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (s0A, (s1A, (s2A, (s3A, (s4A, (s5A, (s0i, (F, (fc, (m, (n, (t, (c, (cnt, (AB, (UB, (PG, (pgw, (lo, (b0, (b1, (szh, (szl, (ctxj, (sz, (maxc, (csz, (stj, (j1, (j2, (pj, (sj, (sjunk, (uj, (fr0, (junk2, (tb, tr))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) as _.
 cbv zeta.
  intros HspA ST CEIL LO MI TP N PRIM AC PC PP FLG HK MCS CF34 CX8 TT0 UW STATS LSJ CX0 CX1 CXS T0 T1 TAL TS CT2
         HC CRa STSa HUB ABLO UBHI AB16 NSZ HPG HPW SB1 SB2 SB3 SB4 HDR B1 UJ LH SHA SHU SHP
         DJT DJC DJN DJS XTAB DTN DTS DCN DCS XTNO XTST N0 N1 R0 R1 FRa FR16 SS SZ SZB TB LTB TRF TRU S47 FRS DEP
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
  unfold AIMG_HI, AINSTANCE, ATP88, ATSD, ATSDI, ATSDK, AINITED, ARSSLIM, AMALLOC_PC in *.
  word_range sp SPR.
  box DJT. box DJC. box DJN. box DJS. box DTN. box DTS. box DCN. box DCS. box CT2.
  (* [comment removed for export] *)
  replace (bv_unsigned sp - 2272) with (bv_unsigned spA + -128) in ST, FRa by lia.
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (allocBC_gen DI L RNG spA gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m n (bv_unsigned sp + -2128) t AB UB PG pgw lo b0 b1 szh szl ctxj sz 353308 pj sjunk tb tr fr0 _ _ _ _ _ _ _ _ _ _ _ _ _).
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
  { eapply (allocD_gen L RNG spA gp tp F fc m2 n t c AB UB lo b0 (hdr_b1_mid b1) id (bv_unsigned sp + -2128) sj uj j1 j2 fr0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
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
  cbv beta. intros ms3 PD. unfold allocD_postG in PD.
  (nd_pre PD 17%nat; intros t0d t1d t2d a1d a2d a3d a4d a5d a6d a7d t3d t4d t5d t6d m3 sj3 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 9%nat; intros MUd WMd MId STd STATSd LSJd UFd HDRd LHd; nd_post).
  rewrite ?HspA in MUd.
  xport CRa MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; lia). xport STSa MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; lia).
  xport SHUb MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia). xport UW MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; lia).   (* [comment removed for export] *)
  xport FR16 MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia). xport SS MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia). xport FRS MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia). xport TB MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; rewrite LTB; lia).
  assert (SHPd : n mod 8 <> 0 -> rw_cells asegs m3 PG [C1 (Z_to_bv 8 (n mod 8))]).
  { intros NE. specialize (SHPb NE). xport SHPb MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS NE; lia). exact SHPb. }
  assert (LH4 : 16 < rz_size n -> rw_cells asegs m3 AB [C8 (Z_to_bv 64 0xCC6E96B9CC6E96B9); C8 (Z_to_bv 64 (UB + -16))]).
  { intros RZ. exact (LHd RZ). }
  assert (DEPd : ADEPOT DI L m3).
  { eapply (adi_frame DI); [exact DEPb | exact MUd | exact WMd |].
    repeat (apply Forall_cons; [cbn [fst snd]; intros a Ha; first [clear -Ha HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RSR NSR HPG PW01 SB1 SB2 SB3 SB4 C16 LSJ N DTN DTS DJN DJS; ub DTN; ub DTS; ub DJN; ub DJS; lia | ub DTN; ub DTS; ub DJN; ub DJS; lia]|]). apply Forall_nil. }   (* [comment removed for export] *)
  (* [comment removed for export] *)
  replace (ret_pc (Z_to_bv 64 0x33bd8)) with (Z_to_bv 64 0x33bd8) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  assert (EspA : spA = Z_to_bv 64 (bv_unsigned sp + -2144)).
  { enough (E : Z_to_bv 64 (bv_unsigned spA) = Z_to_bv 64 (bv_unsigned sp + -2144)) by (rewrite Z_to_bv_bv_unsigned in E; exact E).
    apply Z_to_bv_eqm. rewrite HspA. zeq. }
  rewrite EspA. rewrite HspA in STd. replace (bv_unsigned sp - 2144) with (bv_unsigned sp + -2144) in STd by lia.
  apply rw_cells_of_u64arr in TB. rewrite LTB in TB.
  eapply evtF_mono.
  { eapply (icptC_spec RNG sp gp tp); [exact STd | atop_facts; lia | lia | exact MId | atop_facts; lia | exact FR16
      | eexists; split; [exact SS | reflexivity]
      | eexists; split; [replace (bv_unsigned sp + -2112) with (bv_unsigned sp + -2128 + 16) by lia; exact TB | reflexivity]
      | exact FRS | exact RIMG | exact RTLS | solve_rng ]. }
  cbv beta. intros ms5 PCC. (nd_pre PCC 2%nat; intros m5 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 4%nat; intros MUc WMc MIc STc; nd_post).
  (* [comment removed for export] *)
  xport CRa MUc WMc ltac:(exact I). xport STSa MUc WMc ltac:(exact I). xport STATSd MUc WMc ltac:(exact I).
  xport HDRd MUc WMc ltac:(exact I). xport UFd MUc WMc ltac:(exact I). xport SHUb MUc WMc ltac:(exact I). xport UW MUc WMc ltac:(exact I).
  assert (LH5 : 16 < rz_size n -> rw_cells asegs m5 AB [C8 (Z_to_bv 64 0xCC6E96B9CC6E96B9); C8 (Z_to_bv 64 (UB + -16))]).
  { intros RZ. specialize (LH4 RZ). xport LH4 MUc WMc ltac:(exact I). exact LH4. }
  assert (SHP5 : n mod 8 <> 0 -> rw_cells asegs m5 PG [C1 (Z_to_bv 8 (n mod 8))]).
  { intros NE. specialize (SHPd NE). xport SHPd MUc WMc ltac:(exact I). exact SHPd. }
  assert (DEP5 : ADEPOT DI L m5). { eapply (adi_frame DI); [exact DEPd | exact MUc | exact WMc | apply Forall_nil]. }
  assert (MU : munch (malloc_W L sp t c AB UB PG pgw n) m m5).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUc]].
    eapply munch_trans; [| eapply munch_weaken; [| exact MUd]].
    eapply munch_weaken; [| exact MUb].
    all: first [clear -N C16 PW01 HspA; unfold sub_fp; cbn [outside]; intros q Hq; lia | fp_cover8 | unfold sub_fp; cbn [outside]; intros q Hq; lia]. }   (* [comment removed for export] *)
  assert (WM : wmono asegs m m5).
  { eapply wmono_trans; [exact WMb|]. eapply wmono_trans; [exact WMd| exact WMc]. }
  unfold malloc_post_gen. exists id. do 14 eexists. exists m5, sj3, stj. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MIc|]. split; [exact STc|]. split; [exact IDR|].
  split; [exact CRa|]. split; [exact STSa|]. split; [exact STATSd|]. split; [exact LSJd|]. split; [exact UW|].
  split; [exact HDRd|]. split; [exact UFd|]. split; [exact LH5|]. split; [exact SHUb|]. split; [exact SHP5|]. exact DEP5.
  Unshelve. all: try exact STb; try exact ST.
Qed.
End Zd1.
#[using="Type"] Lemma malloc_tail_gen : ltac:(let t := eval cbv delta [malloc_tail_gen__stmt] in malloc_tail_gen__stmt in exact t).
Proof. exact malloc_tail_gen__body. Qed.
End WithDepot.
End CANSEC1.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_aalloc2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aunwind.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc__A3W.F_aalloc.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_amalloc_iseg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc__A3W.F_amalloc_icpt.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_aalloc2g.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3g.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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
Definition malloc_post_gen (L : alayout) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (n t c cnt AB UB PG pgw lo b1 : Z) (maxc csz : word) (uj : list byte) (m : amem) : machine_state -> Prop :=
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
    /\ rw_cells asegs m' UB [CB (Z.to_nat n) (repeat (Z_to_bv 8 0xbe) (Z.to_nat (Z.min n 4096)) ++ skipn (Z.to_nat (Z.min n 4096)) uj)]
    /\ (16 < rz_size n -> rw_cells asegs m' AB [C8 (Z_to_bv 64 0xCC6E96B9CC6E96B9); C8 (Z_to_bv 64 (UB + -16))])
    /\ rw_cells asegs m' (shad UB) [CB (Z.to_nat (shlen (n - n mod 8))) (repeat (Z_to_bv 8 0) (Z.to_nat (shlen (n - n mod 8))))]
    /\ (n mod 8 <> 0 -> rw_cells asegs m' PG [C1 (Z_to_bv 8 (n mod 8))])
    /\ ADEPOT DI L m'.

Definition malloc_tail_gen__stmt : Prop := forall (L : alayout) RNG (ra sp gp tp spA : word) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0A s1A s2A s3A s4A s5A s0i : word)
    (F : bvmap 5 word) fc (m : amem)
    (n t c cnt AB UB PG pgw lo b0 b1 szh szl ctxj sz : Z) (maxc csz stj j1 j2 : word) (pj : byte)
    (sj : list word) (sjunk uj fr0 junk2 : list byte) (tb : list word) (tr : list Z),
  let ctx := al_ctx L in
  bv_unsigned spA = bv_unsigned sp - 2144 ->
  stk asegs m lo (bv_unsigned sp - 2272) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
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
  rw_cells asegs m (bv_unsigned sp - 2272)
     [CB 8 fr0; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 16); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5A;
      C8 s4A; C8 s3A; C8 s2A; C8 s1A; C8 s0A; C8 (Z_to_bv 64 0x33c40)] ->
  rw_cells asegs m (bv_unsigned sp + -2144) [C8 s0i; C8 (Z_to_bv 64 0x564f0)] ->
  rw_cells asegs m (bv_unsigned sp + -2128) [C8 (Z_to_bv 64 (bv_unsigned sp + -2128 + 16)); C8 (Z_to_bv 64 sz)] ->
  sz = 1 + Z.of_nat (length tr) -> sz <= 255 ->
  u64arr asegs m (bv_unsigned sp + -2128 + 16) tb -> length tb = 255%nat ->
  map bv_unsigned (firstn (Datatypes.S (length tr)) tb) = AMALLOC_PC :: tr ->
  In (AMALLOC_PC :: tr) (al_U L) -> bv_unsigned sp < 2^47 ->
  rw_cells asegs m (bv_unsigned sp + -72) [C8 sp; CB 8 junk2; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ADEPOT DI L m ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 ->
  rng RNG (UB - 16) (n + 16) -> rng RNG AB 16 -> rng RNG (shad AB) 1 -> rng RNG (shad UB) (shlen (n - n mod 8)) -> (n mod 8 <> 0 -> rng RNG PG 1) ->
  AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L ->      (* [comment removed for export] *)
  evtF asegs RNG (malloc_post_gen L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n t c cnt AB UB PG pgw lo b1 maxc csz uj m)
    (MS (mkR (Z_to_bv 64 0x33f10) (Z_to_bv 64 (bv_unsigned spA + -128)) gp tp t0 t1 t2
             (Z_to_bv 64 1) (Z_to_bv 64 n) (Z_to_bv 64 AB) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 8) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n)
             (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 t) (Z_to_bv 64 1)
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x33f10) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 5).
Variable spA : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 6).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 7).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 8).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 9).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 10).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 11).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 12).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 13).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 14).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 15).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 16).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 17).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 18).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 19).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 20).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 21).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 22).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 23).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 24).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 25).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 26).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 27).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 28).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 29).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 30).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 31).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 32).
Variable s0A : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 33).
Variable s1A : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 34).
Variable s2A : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 35).
Variable s3A : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 36).
Variable s4A : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 37).
Variable s5A : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 38).
Variable s0i : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 39).
Variable F : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 40).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 41).
Variable m : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 42).
Variable n : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 43).
Variable t : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 44).
Variable c : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 45).
Variable cnt : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 46).
Variable AB : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 47).
Variable UB : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 48).
Variable PG : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 49).
Variable pgw : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 50).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 51).
Variable b0 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 52).
Variable b1 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 53).
Variable szh : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 54).
Variable szl : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 55).
Variable ctxj : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 56).
Variable sz : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 57).
Variable maxc : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 58).
Variable csz : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 59).
Variable stj : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 60).
Variable j1 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 61).
Variable j2 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 62).
Variable pj : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 63).
Variable sj : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 64).
Variable sjunk : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 65).
Variable uj : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 66).
Variable fr0 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 67).
Variable junk2 : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 68).
Variable tb : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 69).
Variable tr : ltac2:(SecDietF.SzSecF.ty 'malloc_tail_gen__stmt 70).
#[using="Type"] Lemma malloc_tail_gen__body : ltac:(let T := type of (fun (h : malloc_tail_gen__stmt) => h L RNG ra sp gp tp spA t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0A s1A s2A s3A s4A s5A s0i F fc m n t c cnt AB UB PG pgw lo b0 b1 szh szl ctxj sz maxc csz stj j1 j2 pj sj sjunk uj fr0 junk2 tb tr) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (ra, (sp, (gp, (tp, (spA, (t0, (t1, (t2, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (t3, (t4, (t5, (t6, (s0, (s1, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (s0A, (s1A, (s2A, (s3A, (s4A, (s5A, (s0i, (F, (fc, (m, (n, (t, (c, (cnt, (AB, (UB, (PG, (pgw, (lo, (b0, (b1, (szh, (szl, (ctxj, (sz, (maxc, (csz, (stj, (j1, (j2, (pj, (sj, (sjunk, (uj, (fr0, (junk2, (tb, tr))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) as _.
 cbv zeta.
  intros HspA ST CEIL LO MI TP N PRIM AC PC PP FLG HK MCS CF34 CX8 TT0 UW STATS LSJ CX0 CX1 CXS T0 T1 TAL TS CT2
         HC CRa STSa HUB ABLO UBHI AB16 NSZ HPG HPW SB1 SB2 SB3 SB4 HDR B1 UJ LH SHA SHU SHP
         DJT DJC DJN DJS XTAB DTN DTS DCN DCS XTNO XTST N0 N1 R0 R1 FRa FR16 SS SZ SZB TB LTB TRF TRU S47 FRS DEP
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
  unfold AIMG_HI, AINSTANCE, ATP88, ATSD, ATSDI, ATSDK, AINITED, ARSSLIM, AMALLOC_PC in *.
  word_range sp SPR.
  box DJT. box DJC. box DJN. box DJS. box DTN. box DTS. box DCN. box DCS. box CT2.
  (* [comment removed for export] *)
  replace (bv_unsigned sp - 2272) with (bv_unsigned spA + -128) in ST, FRa by lia.
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (allocBC_gen DI L RNG spA gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m n (bv_unsigned sp + -2128) t AB UB PG pgw lo b0 b1 szh szl ctxj sz 353412 pj sjunk tb tr fr0 _ _ _ _ _ _ _ _ _ _ _ _ _).
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
  { eapply (allocD_gen L RNG spA gp tp F fc m2 n t c AB UB lo b0 (hdr_b1_mid b1) id (bv_unsigned sp + -2128) sj uj j1 j2 fr0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
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
  cbv beta. intros ms3 PD. unfold allocD_postG in PD.
  (nd_pre PD 17%nat; intros t0d t1d t2d a1d a2d a3d a4d a5d a6d a7d t3d t4d t5d t6d m3 sj3 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 9%nat; intros MUd WMd MId STd STATSd LSJd UFd HDRd LHd; nd_post).
  rewrite ?HspA in MUd.
  xport CRa MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; lia). xport STSa MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; lia).
  xport SHUb MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia). xport UW MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; lia).   (* [comment removed for export] *)
  xport FR16 MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia). xport SS MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia). xport FRS MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia). xport TB MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; rewrite LTB; lia).
  assert (SHPd : n mod 8 <> 0 -> rw_cells asegs m3 PG [C1 (Z_to_bv 8 (n mod 8))]).
  { intros NE. specialize (SHPb NE). xport SHPb MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS NE; lia). exact SHPb. }
  assert (LH4 : 16 < rz_size n -> rw_cells asegs m3 AB [C8 (Z_to_bv 64 0xCC6E96B9CC6E96B9); C8 (Z_to_bv 64 (UB + -16))]).
  { intros RZ. exact (LHd RZ). }
  assert (DEPd : ADEPOT DI L m3).
  { eapply (adi_frame DI); [exact DEPb | exact MUd | exact WMd |].
    repeat (apply Forall_cons; [cbn [fst snd]; intros a Ha; first [clear -Ha HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RSR NSR HPG PW01 SB1 SB2 SB3 SB4 C16 LSJ N DTN DTS DJN DJS; ub DTN; ub DTS; ub DJN; ub DJS; lia | ub DTN; ub DTS; ub DJN; ub DJS; lia]|]). apply Forall_nil. }   (* [comment removed for export] *)
  (* [comment removed for export] *)
  replace (ret_pc (Z_to_bv 64 0x33c40)) with (Z_to_bv 64 0x33c40) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  assert (EspA : spA = Z_to_bv 64 (bv_unsigned sp + -2144)).
  { enough (E : Z_to_bv 64 (bv_unsigned spA) = Z_to_bv 64 (bv_unsigned sp + -2144)) by (rewrite Z_to_bv_bv_unsigned in E; exact E).
    apply Z_to_bv_eqm. rewrite HspA. zeq. }
  rewrite EspA. rewrite HspA in STd. replace (bv_unsigned sp - 2144) with (bv_unsigned sp + -2144) in STd by lia.
  apply rw_cells_of_u64arr in TB. rewrite LTB in TB.
  eapply evtF_mono.
  { eapply (icptC_spec RNG sp gp tp); [exact STd | atop_facts; lia | lia | exact MId | atop_facts; lia | exact FR16
      | eexists; split; [exact SS | reflexivity]
      | eexists; split; [replace (bv_unsigned sp + -2112) with (bv_unsigned sp + -2128 + 16) by lia; exact TB | reflexivity]
      | exact FRS | exact RIMG | exact RTLS | solve_rng ]. }
  cbv beta. intros ms5 PCC. (nd_pre PCC 2%nat; intros m5 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 4%nat; intros MUc WMc MIc STc; nd_post).
  (* [comment removed for export] *)
  xport CRa MUc WMc ltac:(exact I). xport STSa MUc WMc ltac:(exact I). xport STATSd MUc WMc ltac:(exact I).
  xport HDRd MUc WMc ltac:(exact I). xport UFd MUc WMc ltac:(exact I). xport SHUb MUc WMc ltac:(exact I). xport UW MUc WMc ltac:(exact I).
  assert (LH5 : 16 < rz_size n -> rw_cells asegs m5 AB [C8 (Z_to_bv 64 0xCC6E96B9CC6E96B9); C8 (Z_to_bv 64 (UB + -16))]).
  { intros RZ. specialize (LH4 RZ). xport LH4 MUc WMc ltac:(exact I). exact LH4. }
  assert (SHP5 : n mod 8 <> 0 -> rw_cells asegs m5 PG [C1 (Z_to_bv 8 (n mod 8))]).
  { intros NE. specialize (SHPd NE). xport SHPd MUc WMc ltac:(exact I). exact SHPd. }
  assert (DEP5 : ADEPOT DI L m5). { eapply (adi_frame DI); [exact DEPd | exact MUc | exact WMc | apply Forall_nil]. }
  assert (MU : munch (malloc_W L sp t c AB UB PG pgw n) m m5).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUc]].
    eapply munch_trans; [| eapply munch_weaken; [| exact MUd]].
    eapply munch_weaken; [| exact MUb].
    all: first [clear -N C16 PW01 HspA; unfold sub_fp; cbn [outside]; intros q Hq; lia | fp_cover8 | unfold sub_fp; cbn [outside]; intros q Hq; lia]. }   (* [comment removed for export] *)
  assert (WM : wmono asegs m m5).
  { eapply wmono_trans; [exact WMb|]. eapply wmono_trans; [exact WMd| exact WMc]. }
  unfold malloc_post_gen. exists id. do 14 eexists. exists m5, sj3, stj. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MIc|]. split; [exact STc|]. split; [exact IDR|].
  split; [exact CRa|]. split; [exact STSa|]. split; [exact STATSd|]. split; [exact LSJd|]. split; [exact UW|].
  split; [exact HDRd|]. split; [exact UFd|]. split; [exact LH5|]. split; [exact SHUb|]. split; [exact SHP5|]. exact DEP5.
  Unshelve. all: try exact STb; try exact ST.
Qed.
End Zd1.
#[using="Type"] Lemma malloc_tail_gen : ltac:(let t := eval cbv delta [malloc_tail_gen__stmt] in malloc_tail_gen__stmt in exact t).
Proof. exact malloc_tail_gen__body. Qed.
End WithDepot.
End CANSEC1.
(* [comment removed for export] *)
End TwB.
End F_amalloc_tailg.

(* [comment removed for export] *)
Module F_aallocfn_tailg.
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecSlog__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_agbb__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3 F_aunwind. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_s__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3g. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_aalloc2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aunwind OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc__A3W.F_aalloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_amalloc_iseg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc__A3W.F_amalloc_icpt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_aalloc2g OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3g OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3g0__A3W.F_amalloc_tailg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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

Definition allocfn_tail_gen__stmt : Prop := forall (L : alayout) RNG (raA gp tp spA : word) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    (s6 s7 s8 s9 s10 s11 s0A s1A s2A s3A s4A s5A : word)
    (F : bvmap 5 word) fc (m : amem)
    (n t c cnt AB UB PG pgw lo b0 b1 szh szl ctxj sz S pc : Z) (maxc csz stj j1 j2 : word) (pj : byte)
    (sj : list word) (sjunk uj fr0 : list byte) (tb : list word) (tr : list Z),
  let ctx := al_ctx L in
  bv_unsigned spA <= S ->
  stk asegs m lo (bv_unsigned spA + -128) -> ATOP <= lo -> lo <= bv_unsigned spA - 1952 ->
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
  rw_cells asegs m (bv_unsigned spA + -128)
     [CB 8 fr0; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 16); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5A;
      C8 s4A; C8 s3A; C8 s2A; C8 s1A; C8 s0A; C8 raA] ->
  rw_cells asegs m S [C8 (Z_to_bv 64 (S + 16)); C8 (Z_to_bv 64 sz)] ->
  sz = 1 + Z.of_nat (length tr) -> sz <= 255 ->
  u64arr asegs m (S + 16) tb -> length tb = 255%nat ->
  map bv_unsigned (firstn (Datatypes.S (length tr)) tb) = pc :: tr ->
  In (pc :: tr) (al_U L) -> S + 2056 <= 2^47 ->
  ADEPOT DI L m ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned spA - lo) -> rng RNG S 2056 -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 ->
  rng RNG (UB - 16) (n + 16) -> rng RNG AB 16 -> rng RNG (shad AB) 1 -> rng RNG (shad UB) (shlen (n - n mod 8)) -> (n mod 8 <> 0 -> rng RNG PG 1) ->
  AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L ->      (* [comment removed for export] *)
  evtF asegs RNG (malloc_post_gen DI L raA spA gp tp s0A s1A s2A s3A s4A s5A s6 s7 s8 s9 s10 s11 F fc n t c cnt AB UB PG pgw lo b1 maxc csz uj m)
    (MS (mkR (Z_to_bv 64 0x33ea8) (Z_to_bv 64 (bv_unsigned spA + -128)) gp tp t0 t1 t2
             (Z_to_bv 64 1) (Z_to_bv 64 n) (Z_to_bv 64 AB) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 8) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n)
             (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 S) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 t) (Z_to_bv 64 1)
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x33ea8) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 1).
Variable raA : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 2).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 3).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 4).
Variable spA : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 5).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 6).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 7).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 8).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 9).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 10).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 11).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 12).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 13).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 14).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 15).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 16).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 17).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 18).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 19).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 20).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 21).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 22).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 23).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 24).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 25).
Variable s0A : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 26).
Variable s1A : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 27).
Variable s2A : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 28).
Variable s3A : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 29).
Variable s4A : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 30).
Variable s5A : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 31).
Variable F : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 32).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 33).
Variable m : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 34).
Variable n : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 35).
Variable t : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 36).
Variable c : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 37).
Variable cnt : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 38).
Variable AB : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 39).
Variable UB : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 40).
Variable PG : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 41).
Variable pgw : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 42).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 43).
Variable b0 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 44).
Variable b1 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 45).
Variable szh : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 46).
Variable szl : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 47).
Variable ctxj : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 48).
Variable sz : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 49).
Variable S : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 50).
Variable pc : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 51).
Variable maxc : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 52).
Variable csz : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 53).
Variable stj : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 54).
Variable j1 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 55).
Variable j2 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 56).
Variable pj : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 57).
Variable sj : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 58).
Variable sjunk : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 59).
Variable uj : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 60).
Variable fr0 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 61).
Variable tb : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 62).
Variable tr : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 63).
#[using="Type"] Lemma allocfn_tail_gen__body : ltac:(let T := type of (fun (h : allocfn_tail_gen__stmt) => h L RNG raA gp tp spA t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s6 s7 s8 s9 s10 s11 s0A s1A s2A s3A s4A s5A F fc m n t c cnt AB UB PG pgw lo b0 b1 szh szl ctxj sz S pc maxc csz stj j1 j2 pj sj sjunk uj fr0 tb tr) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (raA, (gp, (tp, (spA, (t0, (t1, (t2, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (t3, (t4, (t5, (t6, (s6, (s7, (s8, (s9, (s10, (s11, (s0A, (s1A, (s2A, (s3A, (s4A, (s5A, (F, (fc, (m, (n, (t, (c, (cnt, (AB, (UB, (PG, (pgw, (lo, (b0, (b1, (szh, (szl, (ctxj, (sz, (S, (pc, (maxc, (csz, (stj, (j1, (j2, (pj, (sj, (sjunk, (uj, (fr0, (tb, tr)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) as _.
 cbv zeta.
  intros HspA ST CEIL LO MI TP N PRIM AC PC PP FLG HK MCS CF34 CX8 TT0 UW STATS LSJ CX0 CX1 CXS T0 T1 TAL TS CT2
         HC CRa STSa HUB ABLO UBHI AB16 NSZ HPG HPW SB1 SB2 SB3 SB4 HDR B1 UJ LH SHA SHU SHP
         DJT DJC DJN DJS XTAB DTN DTS DCN DCS XTNO XTST N0 N1 R0 R1 FRa SS SZ SZB TB LTB TRF TRU S47 DEP
         RIMG RTLS RSTK RS RCTX RT RNO RST RU RAB RSA RSU RSP NI SI. band_lin.   (* [comment removed for export] *)
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
  unfold AIMG_HI, AINSTANCE, ATP88, ATSD, ATSDI, ATSDK, AINITED, ARSSLIM in *.
  word_range spA SPR.
  box DJT. box DJC. box DJN. box DJS. box DTN. box DTS. box DCN. box DCS. box CT2.
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (allocBC_gen DI L RNG spA gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m n S t AB UB PG pgw lo b0 b1 szh szl ctxj sz pc pj sjunk tb tr fr0 _ _ _ _ _ _ _ _ _ _ _ _ _).
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
  (* [comment removed for export] *)
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
  xport SS MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia). xport TB MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; rewrite LTB; lia).
  assert (LH2 : 16 < rz_size n -> rw_cells asegs m2 AB [C8 j1; C8 j2]).
  { intros RZ. specialize (LH RZ). pose proof (rz_size_cases n) as RZC.
    xport LH MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS RZ RZC; ub DJN; ub DJS; lia_relc). exact LH. }
  clear LH SHP.
  pose proof (hdr_b1_mid_range b1 ltac:(lia)) as B1M.
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (allocD_gen L RNG spA gp tp F fc m2 n t c AB UB lo b0 (hdr_b1_mid b1) id S sj uj j1 j2 fr0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
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
  cbv beta. intros ms3 PD. unfold allocD_postG in PD.
  (nd_pre PD 17%nat; intros t0d t1d t2d a1d a2d a3d a4d a5d a6d a7d t3d t4d t5d t6d m3 sj3 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 9%nat; intros MUd WMd MId STd STATSd LSJd UFd HDRd LHd; nd_post).
  xport CRa MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; lia). xport STSa MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; lia).
  xport SHUb MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia). xport UW MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; lia).   (* [comment removed for export] *)
  xport SS MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia). xport TB MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; rewrite LTB; lia).
  assert (SHPd : n mod 8 <> 0 -> rw_cells asegs m3 PG [C1 (Z_to_bv 8 (n mod 8))]).
  { intros NE. specialize (SHPb NE). xport SHPb MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS NE; lia). exact SHPb. }
  assert (LH4 : 16 < rz_size n -> rw_cells asegs m3 AB [C8 (Z_to_bv 64 0xCC6E96B9CC6E96B9); C8 (Z_to_bv 64 (UB + -16))]).
  { intros RZ. exact (LHd RZ). }
  assert (DEPd : ADEPOT DI L m3).
  { eapply (adi_frame DI); [exact DEPb | exact MUd | exact WMd |].
    repeat (apply Forall_cons; [cbn [fst snd]; intros a Ha; first [clear -Ha HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RSR NSR HPG PW01 SB1 SB2 SB3 SB4 C16 LSJ N DTN DTS DJN DJS; ub DTN; ub DTS; ub DJN; ub DJS; lia | ub DTN; ub DTS; ub DJN; ub DJS; lia]|]). apply Forall_nil. }   (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (MU : munch (malloc_W L spA t c AB UB PG pgw n) m m3).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUd]].
    eapply munch_weaken; [| exact MUb].
    all: first [clear -N C16 PW01 HspA; unfold sub_fp; cbn [outside]; intros q Hq; lia | fp_cover8 | unfold sub_fp; cbn [outside]; intros q Hq; lia]. }
  assert (WM : wmono asegs m m3) by (eapply wmono_trans; [exact WMb| exact WMd]).
  apply evtF_done. unfold malloc_post_gen. exists id. do 14 eexists. exists m3, sj3, stj. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MId|]. split; [exact STd|]. split; [exact IDR|].
  split; [exact CRa|]. split; [exact STSa|]. split; [exact STATSd|]. split; [exact LSJd|]. split; [exact UW|].
  split; [exact HDRd|]. split; [exact UFd|]. split; [exact LH4|]. split; [exact SHUb|]. split; [exact SHPd|]. exact DEPd.
  Unshelve. all: try exact STb; try exact ST.
Qed.
End Zd1.
#[using="Type"] Lemma allocfn_tail_gen : ltac:(let t := eval cbv delta [allocfn_tail_gen__stmt] in allocfn_tail_gen__stmt in exact t).
Proof. exact allocfn_tail_gen__body. Qed.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_aalloc2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aunwind.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc__A3W.F_aalloc.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_amalloc_iseg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc__A3W.F_amalloc_icpt.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_aalloc2g.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3g.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3g0__A3W.F_amalloc_tailg.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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

Definition allocfn_tail_gen__stmt : Prop := forall (L : alayout) RNG (raA gp tp spA : word) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    (s6 s7 s8 s9 s10 s11 s0A s1A s2A s3A s4A s5A : word)
    (F : bvmap 5 word) fc (m : amem)
    (n t c cnt AB UB PG pgw lo b0 b1 szh szl ctxj sz S pc : Z) (maxc csz stj j1 j2 : word) (pj : byte)
    (sj : list word) (sjunk uj fr0 : list byte) (tb : list word) (tr : list Z),
  let ctx := al_ctx L in
  bv_unsigned spA <= S ->
  stk asegs m lo (bv_unsigned spA + -128) -> ATOP <= lo -> lo <= bv_unsigned spA - 1952 ->
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
  rw_cells asegs m (bv_unsigned spA + -128)
     [CB 8 fr0; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 16); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5A;
      C8 s4A; C8 s3A; C8 s2A; C8 s1A; C8 s0A; C8 raA] ->
  rw_cells asegs m S [C8 (Z_to_bv 64 (S + 16)); C8 (Z_to_bv 64 sz)] ->
  sz = 1 + Z.of_nat (length tr) -> sz <= 255 ->
  u64arr asegs m (S + 16) tb -> length tb = 255%nat ->
  map bv_unsigned (firstn (Datatypes.S (length tr)) tb) = pc :: tr ->
  In (pc :: tr) (al_U L) -> S + 2056 <= 2^47 ->
  ADEPOT DI L m ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned spA - lo) -> rng RNG S 2056 -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 ->
  rng RNG (UB - 16) (n + 16) -> rng RNG AB 16 -> rng RNG (shad AB) 1 -> rng RNG (shad UB) (shlen (n - n mod 8)) -> (n mod 8 <> 0 -> rng RNG PG 1) ->
  AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L ->      (* [comment removed for export] *)
  evtF asegs RNG (malloc_post_gen DI L raA spA gp tp s0A s1A s2A s3A s4A s5A s6 s7 s8 s9 s10 s11 F fc n t c cnt AB UB PG pgw lo b1 maxc csz uj m)
    (MS (mkR (Z_to_bv 64 0x33f10) (Z_to_bv 64 (bv_unsigned spA + -128)) gp tp t0 t1 t2
             (Z_to_bv 64 1) (Z_to_bv 64 n) (Z_to_bv 64 AB) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 8) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n)
             (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 S) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 t) (Z_to_bv 64 1)
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x33f10) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 1).
Variable raA : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 2).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 3).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 4).
Variable spA : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 5).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 6).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 7).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 8).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 9).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 10).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 11).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 12).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 13).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 14).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 15).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 16).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 17).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 18).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 19).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 20).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 21).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 22).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 23).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 24).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 25).
Variable s0A : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 26).
Variable s1A : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 27).
Variable s2A : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 28).
Variable s3A : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 29).
Variable s4A : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 30).
Variable s5A : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 31).
Variable F : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 32).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 33).
Variable m : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 34).
Variable n : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 35).
Variable t : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 36).
Variable c : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 37).
Variable cnt : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 38).
Variable AB : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 39).
Variable UB : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 40).
Variable PG : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 41).
Variable pgw : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 42).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 43).
Variable b0 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 44).
Variable b1 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 45).
Variable szh : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 46).
Variable szl : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 47).
Variable ctxj : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 48).
Variable sz : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 49).
Variable S : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 50).
Variable pc : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 51).
Variable maxc : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 52).
Variable csz : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 53).
Variable stj : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 54).
Variable j1 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 55).
Variable j2 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 56).
Variable pj : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 57).
Variable sj : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 58).
Variable sjunk : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 59).
Variable uj : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 60).
Variable fr0 : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 61).
Variable tb : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 62).
Variable tr : ltac2:(SecDietF.SzSecF.ty 'allocfn_tail_gen__stmt 63).
#[using="Type"] Lemma allocfn_tail_gen__body : ltac:(let T := type of (fun (h : allocfn_tail_gen__stmt) => h L RNG raA gp tp spA t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s6 s7 s8 s9 s10 s11 s0A s1A s2A s3A s4A s5A F fc m n t c cnt AB UB PG pgw lo b0 b1 szh szl ctxj sz S pc maxc csz stj j1 j2 pj sj sjunk uj fr0 tb tr) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (raA, (gp, (tp, (spA, (t0, (t1, (t2, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (t3, (t4, (t5, (t6, (s6, (s7, (s8, (s9, (s10, (s11, (s0A, (s1A, (s2A, (s3A, (s4A, (s5A, (F, (fc, (m, (n, (t, (c, (cnt, (AB, (UB, (PG, (pgw, (lo, (b0, (b1, (szh, (szl, (ctxj, (sz, (S, (pc, (maxc, (csz, (stj, (j1, (j2, (pj, (sj, (sjunk, (uj, (fr0, (tb, tr)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) as _.
 cbv zeta.
  intros HspA ST CEIL LO MI TP N PRIM AC PC PP FLG HK MCS CF34 CX8 TT0 UW STATS LSJ CX0 CX1 CXS T0 T1 TAL TS CT2
         HC CRa STSa HUB ABLO UBHI AB16 NSZ HPG HPW SB1 SB2 SB3 SB4 HDR B1 UJ LH SHA SHU SHP
         DJT DJC DJN DJS XTAB DTN DTS DCN DCS XTNO XTST N0 N1 R0 R1 FRa SS SZ SZB TB LTB TRF TRU S47 DEP
         RIMG RTLS RSTK RS RCTX RT RNO RST RU RAB RSA RSU RSP NI SI. band_lin.   (* [comment removed for export] *)
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
  unfold AIMG_HI, AINSTANCE, ATP88, ATSD, ATSDI, ATSDK, AINITED, ARSSLIM in *.
  word_range spA SPR.
  box DJT. box DJC. box DJN. box DJS. box DTN. box DTS. box DCN. box DCS. box CT2.
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (allocBC_gen DI L RNG spA gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m n S t AB UB PG pgw lo b0 b1 szh szl ctxj sz pc pj sjunk tb tr fr0 _ _ _ _ _ _ _ _ _ _ _ _ _).
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
  (* [comment removed for export] *)
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
  xport SS MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia). xport TB MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; rewrite LTB; lia).
  assert (LH2 : 16 < rz_size n -> rw_cells asegs m2 AB [C8 j1; C8 j2]).
  { intros RZ. specialize (LH RZ). pose proof (rz_size_cases n) as RZC.
    xport LH MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS RZ RZC; ub DJN; ub DJS; lia_relc). exact LH. }
  clear LH SHP.
  pose proof (hdr_b1_mid_range b1 ltac:(lia)) as B1M.
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (allocD_gen L RNG spA gp tp F fc m2 n t c AB UB lo b0 (hdr_b1_mid b1) id S sj uj j1 j2 fr0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
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
  cbv beta. intros ms3 PD. unfold allocD_postG in PD.
  (nd_pre PD 17%nat; intros t0d t1d t2d a1d a2d a3d a4d a5d a6d a7d t3d t4d t5d t6d m3 sj3 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 9%nat; intros MUd WMd MId STd STATSd LSJd UFd HDRd LHd; nd_post).
  xport CRa MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; lia). xport STSa MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; lia).
  xport SHUb MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia). xport UW MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; lia).   (* [comment removed for export] *)
  xport SS MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS LABND LNBND LSBND; lia). xport TB MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; rewrite LTB; lia).
  assert (SHPd : n mod 8 <> 0 -> rw_cells asegs m3 PG [C1 (Z_to_bv 8 (n mod 8))]).
  { intros NE. specialize (SHPb NE). xport SHPb MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS NE; lia). exact SHPb. }
  assert (LH4 : 16 < rz_size n -> rw_cells asegs m3 AB [C8 (Z_to_bv 64 0xCC6E96B9CC6E96B9); C8 (Z_to_bv 64 (UB + -16))]).
  { intros RZ. exact (LHd RZ). }
  assert (DEPd : ADEPOT DI L m3).
  { eapply (adi_frame DI); [exact DEPb | exact MUd | exact WMd |].
    repeat (apply Forall_cons; [cbn [fst snd]; intros a Ha; first [clear -Ha HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RSR NSR HPG PW01 SB1 SB2 SB3 SB4 C16 LSJ N DTN DTS DJN DJS; ub DTN; ub DTS; ub DJN; ub DJS; lia | ub DTN; ub DTS; ub DJN; ub DJS; lia]|]). apply Forall_nil. }   (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (MU : munch (malloc_W L spA t c AB UB PG pgw n) m m3).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUd]].
    eapply munch_weaken; [| exact MUb].
    all: first [clear -N C16 PW01 HspA; unfold sub_fp; cbn [outside]; intros q Hq; lia | fp_cover8 | unfold sub_fp; cbn [outside]; intros q Hq; lia]. }
  assert (WM : wmono asegs m m3) by (eapply wmono_trans; [exact WMb| exact WMd]).
  apply evtF_done. unfold malloc_post_gen. exists id. do 14 eexists. exists m3, sj3, stj. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MId|]. split; [exact STd|]. split; [exact IDR|].
  split; [exact CRa|]. split; [exact STSa|]. split; [exact STATSd|]. split; [exact LSJd|]. split; [exact UW|].
  split; [exact HDRd|]. split; [exact UFd|]. split; [exact LH4|]. split; [exact SHUb|]. split; [exact SHPd|]. exact DEPd.
  Unshelve. all: try exact STb; try exact ST.
Qed.
End Zd1.
#[using="Type"] Lemma allocfn_tail_gen : ltac:(let t := eval cbv delta [allocfn_tail_gen__stmt] in allocfn_tail_gen__stmt in exact t).
Proof. exact allocfn_tail_gen__body. Qed.
End WithDepot.
End CANSEC1.
(* [comment removed for export] *)
End TwB.
End F_aallocfn_tailg.

(* [comment removed for export] *)
Module F_arealloc_iseg.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecSlog__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_adrain__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_memcpy. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_aintal OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memcpy.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
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


(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition AREALLOC_SYM' : Z := 0x56180.    (* [comment removed for export] *)
Definition AREALLOC_PC' : Z := 0x568f0.     (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ricptA_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (p n lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) m' (junk0 junk1 junk2 : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x56904) (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2
                  sp (Z_to_bv 64 n)
                  (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 0x568f0) sp (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 30) a6 a7
                  (Z_to_bv 64 p) (Z_to_bv 64 0x568f0) (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 (bv_unsigned sp + -89))
                  s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x56948) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2192, bv_unsigned sp); (0xaf800, 0xaf800 + 0x81030); (0x13e088, 0x13e088 + 4)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -2144)
    /\ rw_cells asegs m' (bv_unsigned sp + -2144) [CB 8 junk0]
    /\ rw_cells asegs m' (bv_unsigned sp + -2136) [C8 (Z_to_bv 64 (bv_unsigned sp + -2120)); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]
    /\ rw_cells asegs m' (bv_unsigned sp + -2120) [CB 2040 junk1]
    /\ rw_cells asegs m' (bv_unsigned sp + -80) [C8 sp; CB 8 junk2; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' 0x13e088 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ stk asegs m' 0xaf800 (0xaf800 + 0x81030)
    /\ (forall j, 0 <= j < 32768 -> bytes_at asegs m' (0xaf808 + 8 * j) (le8 (Z_to_bv 64 0))).

Definition ricptA_spec__stmt : Prop := forall (ia : bool) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (p n lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 2192 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 n -> 0 <= p < 2^47 -> 0 <= n < 2^64 ->
  rw_cells asegs m 0xaf2d8 [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m 0xaf2fc [C4 (Z_to_bv 64 30)] ->
  rw_cells asegs m 0xa54a0 [C8 (Z_to_bv 64 0x140128); C8 (Z_to_bv 64 0xabdf8); C8 (Z_to_bv 64 0xae5f8);
                             C8 (Z_to_bv 64 0xaf2e8); C8 (Z_to_bv 64 0xaf2f0); C8 (Z_to_bv 64 0xaf2e0)] ->
  rw_cells asegs m 0x14014a [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m 0xa5490 [C8 (Z_to_bv 64 0x13e0a0)] -> rw_cells asegs m 0x13e0a0 [C8 (Z_to_bv 64 4096)] ->
  (* [comment removed for export] *)
  rw_cells asegs m AIA_FLAG [C1 (Z_to_bv 8 (if ia then 1 else 0)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  stk asegs m AIA_BASE (AIA_BASE + AIA_SIZE) ->
  (ia = true -> forall j, 0 <= j < 32768 -> bytes_at asegs m (AIA_MAP1 + 8 * j) (le8 (Z_to_bv 64 0))) ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (ricptA_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc p n lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AREALLOC_SYM') fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable ia : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 5).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 6).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 7).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 8).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 9).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 10).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 11).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 12).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 13).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 14).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 15).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 16).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 17).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 18).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 19).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 20).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 21).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 22).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 23).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 24).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 25).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 26).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 27).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 28).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 29).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 30).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 31).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 32).
Variable F : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 33).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 34).
Variable m : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 35).
Variable p : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 36).
Variable n : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 37).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 38).
#[using="Type"] Lemma ricptA_spec__body : ltac:(let T := type of (fun (h : ricptA_spec__stmt) => h ia RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p n lo) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (ia, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (p, (n, lo))))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO MI -> -> PR NR INI MCS GOT CF34 PG1 PG2 FL IA Z2 RIMG RTLS RSTK. atop_facts.
  unfold AREALLOC_SYM', AIA_BASE, AIA_SIZE, AIA_FLAG, AIA_MAP1, AIA_MAP1_LEN in *.
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 2192, bv_unsigned sp); (0xaf800, 0xaf800 + 0x81030); (0x13e088, 0x13e088 + 4)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  pose proof (munch_refl [(bv_unsigned sp - 2192, bv_unsigned sp)]%Z m) as MU0.
  step.                                                          (* [comment removed for export] *)
  carve_frame 2144%nat ST.
  lazymatch type of FR with rw_cells ?segs ?mm ?A [CB ?n ?junk] =>
    apply (rw_cells_split_CB segs mm A [] n junk [] [8; 16; 2040; 80]%nat) in FR; [| cbn; lia]; cbn [app mk_CB_cells] in FR end.
  (* [comment removed for export] *)
  repeat match type of FR with context [CB _ ?j] => lazymatch j with firstn _ _ => idtac | skipn _ _ => idtac end;
           let x := fresh "jkf" in set (x := j) in FR; clearbody x end.
  rw_split FR 1%nat FRp FR'. rw_split FR' 1%nat FRa FR''. rw_split FR'' 1%nat FRt FRs.
  do 9 step.                                                     (* [comment removed for export] *)
  zstep. zstep. step. step. step.                                (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. carve_frame 16%nat ST.
  do 5 step. lstep. step. step. step. if_lit.                    (* [comment removed for export] *)
  do 4 step. release_frame FR ST (bv_unsigned sp + -2144).
  step. if_lit.                                                  (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (Z2' : ia = true -> forall j, 0 <= j < 32768 -> bytes_at asegs mm (718856 + 8 * j) (le8 (Z_to_bv 64 0)))
      by (intros Hia j Hj; eapply bytes_at_agree; [exact (Z2 Hia j Hj)|];
          intros i Hi; apply MU0; cbn [outside]; rewrite length_le8 in Hi; rewrite wa_unsigned by lia; lia) end.
  clear Z2 MU0.
  step. call_sp internal_allocator_spec;
    [exact ST| exact CEIL| lia| exact MI| exact FL| exact IA| exact Z2'| exact PG1| exact PG2| solve_rng|].
  try rename MI0 into MI. clear Z2'.
  match goal with H : stk asegs ?mm lo _ |- _ => rename H into ST end.
  match goal with H : stk asegs ?mm 718848 _ |- _ => rename H into IA' end.
  match goal with H : rw_cells asegs ?mm 1302664 _ |- _ => rename H into FL' end.
  match goal with H : forall j, _ -> bytes_at asegs _ _ _ |- _ => rename H into MAP end.
  snapshot [(bv_unsigned sp - 2192, bv_unsigned sp)]%Z MU1 WM1.
  (* [comment removed for export] *)
  zstep. setreg 11%Z (Z_to_bv 64 0) ltac:(f_equal; rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; lia).
  step. if_lit.                                (* [comment removed for export] *)
  zstep.                                       (* [comment removed for export] *)
  remember (Z.shiftr p 32) as j eqn:Hj.
  assert (JR : 0 <= j < 32768) by (subst j; rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
  zstep. rewrite (Z.shiftl_mul_pow2 j 3) by lia. change (2^3) with 8. zstep.   (* [comment removed for export] *)
  pose proof (bytes_at_read8 _ _ _ (MAP j JR)) as RD.
  replace (718856 + 8 * j) with (718848 + j * 8 + 8) in RD by lia.
  step. clear RD.                              (* [comment removed for export] *)
  step. step. if_lit.                          (* [comment removed for export] *)
  clear Hj JR.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep. zstep. zstep.   (* [comment removed for export] *)
  step. sstep. step.                                             (* [comment removed for export] *)
  step. step. lstep. step. step.                                 (* [comment removed for export] *)
  step. step. if_lit.                                            (* [comment removed for export] *)
  step. step. step.                                              (* [comment removed for export] *)
  step. step. lstep. step.                                       (* [comment removed for export] *)
  step. step. lstep. step. step.                                 (* [comment removed for export] *)
  step. zstep. zstep. zstep. step.                               (* [comment removed for export] *)
  change ((Z.b2z (30 <? 1) + -1) mod 18446744073709551616) with 18446744073709551615. rewrite land_ones_l by lia.
  sstep.                                                         (* [comment removed for export] *)
  step. if_lit.                                                  (* [comment removed for export] *)
  zstep. zstep. step. step. step. step.                          (* [comment removed for export] *)
  rw_split FRa 1%nat FRa1 FRa2. apply rw_cells_C8_to_C4C4_zero in FRa2. rw_join FRa1 FRa2 FRA.
  apply evtF_done. unfold ricptA_post. do 13 eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
  split; [exact FRp|]. split; [exact FRA|]. split; [exact FRt|]. split; [exact FRs|]. split; [exact FL'|]. split; [exact IA'|].
  intros j0 Hj0. eapply bytes_at_agree; [exact (MAP j0 Hj0)|].
  intros i Hi. apply MU1. cbn [outside]. rewrite length_le8 in Hi. rewrite wa_unsigned by lia. lia.
Qed.
End Zd1.
#[using="Type"] Lemma ricptA_spec : ltac:(let t := eval cbv delta [ricptA_spec__stmt] in ricptA_spec__stmt in exact t).
Proof. exact ricptA_spec__body. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ricptB_post (sp gp tp s3v s4v s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (p n t lo : Z) (t0 t1 t2 a7 t3 t4 t5 t6 : word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists m' (fr0 : list byte) (sj' : list word),
    ms' = MS (mkR (Z_to_bv 64 0x34788) (Z_to_bv 64 (bv_unsigned sp + -2208)) gp tp t0 t1 t2
                  (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 p)
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 n) (Z_to_bv 64 8) (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 1) (Z_to_bv 64 1)
                  (Z_to_bv 64 (bv_unsigned sp + -2136)) a7
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 n) s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x33c08) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2240, bv_unsigned sp - 2144); (t + 2800, t + 2800 + 368)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -2208)
    /\ rw_cells asegs m' (bv_unsigned sp + -2208) [C8 s4v; C8 s3v; C8 (Z_to_bv 64 p); C8 (Z_to_bv 64 n); C8 sp; C8 (Z_to_bv 64 0x3470c)]
    /\ rw_cells asegs m' (bv_unsigned sp + -2160) [CB 8 fr0; C8 (Z_to_bv 64 0x56960)]
    /\ u64arr asegs m' (t + 2800) sj' /\ length sj' = 46%nat.

#[using="Type"] Lemma ricptB_spec : forall RNG ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (p n ctx t lo : Z) (sj : list word),
  stk asegs m lo (bv_unsigned sp + -2144) -> ATOP <= lo -> lo <= bv_unsigned sp - 2240 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  s1 = Z_to_bv 64 n -> s2 = Z_to_bv 64 p -> 1 <= p < 2^64 -> 1 <= n < 2^64 ->
  rw_cells asegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells asegs m ATSDK [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  0 < ctx -> AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) ->
  (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  evtF asegs RNG (ricptB_post sp gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc p n t lo t0 t1 t2 a7 t3 t4 t5 t6 m)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2 sp s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5694c) fc None m (seg_rom asegs)).
Proof.
  intros until sj. intros ST CEIL LO MI TP -> -> PR NR TI TK T88 TSD CT CX0 C0 C1 T0 T1 CT2 STATS LSJ RIMG RTLS RSTK RCTX RT.
  pose proof T0 as T0'. unfold iclr, AIMG_LO, AIMG_HI in T0'. atop_facts.
  unfold AIMG_HI, AINSTANCE, ATSDI, ATSDK, ATP88, ATSD in *.
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 2240, bv_unsigned sp - 2144); (t + 2800, t + 2800 + 368)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep. step. step. step.                                (* [comment removed for export] *)
  carve_frame 16%nat ST. rename FR into FR16.
  step. step. step. step.                                        (* [comment removed for export] *)
  step. if_cases K0; zify_cond K0. { exfalso. clear -K0 PR. lia. }       (* [comment removed for export] *)
  step.                                                          (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1. 2: { exfalso. clear -K1 NR. lia. }    (* [comment removed for export] *)
  step. zstep. step. step. step.                                 (* [comment removed for export] *)
  carve_frame 48%nat ST.
  do 7 step.                                                     (* [comment removed for export] *)
  step. if_cases K2; zify_cond K2. { exfalso. clear -K2 PR. lia. }       (* [comment removed for export] *)
  step.                                                          (* [comment removed for export] *)
  step. if_cases K3; zify_cond K3. { exfalso. clear -K3 NR. lia. }       (* [comment removed for export] *)
  step. step. step.                                              (* [comment removed for export] *)
  box RT.
  step. call_sp thread_stats_spec;
    [exact ST| exact CEIL| lia| exact MI| exact TP| exact TI| exact TK| exact T88| exact TSD| exact CT| lia| exact C1| exact T0| exact T1| solve_rng|].
  unbox RT. rename POST into ST. try rename MI0 into MI.
  aload STATS 7 (t + 2800 + 56).                                 (* [comment removed for export] *)
  aload STATS 8 (t + 2800 + 64).                                 (* [comment removed for export] *)
  zstep. zstep.                                                  (* [comment removed for export] *)
  astore STATS 7.                                                (* [comment removed for export] *)
  astore STATS 8.                                                (* [comment removed for export] *)
  do 6 step.                                                     (* [comment removed for export] *)
  step.                                                          (* [comment removed for export] *)
  apply evtF_done. unfold ricptB_post, AINSTANCE. do 3 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|]. split; [exact FR16|].
  split; [exact STATS|]. rewrite !upd_length. exact LSJ.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ricptC_post (sp gp tp s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (p NEW n nold S : Z) (bs uj : list byte) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a6 a7 t3 t4 t5 t6 m',
    let mn := Z.min nold n in
    ms' = MS (mkR (Z_to_bv 64 0x3481c) sp gp tp t0 t1 t2
                  (Z_to_bv 64 S) (Z_to_bv 64 p)
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 p) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 S) (Z_to_bv 64 1) a6 a7
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 mn) (Z_to_bv 64 NEW) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x338f4) fc None m' (seg_rom asegs)
    /\ munch [(NEW, NEW + mn)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' NEW [CB (Z.to_nat n) (firstn (Z.to_nat mn) bs ++ skipn (Z.to_nat mn) uj)].

Definition ricptC_spec__stmt : Prop := forall RNG sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (p NEW n nold S b1 actx : Z) (bs uj : list byte),
  mem_inv asegs m ->
  0 < NEW < 2^64 -> 16 <= p -> p + nold < 2^64 -> NEW + n < 2^64 -> 1 <= n < 2^32 -> 1 <= nold < 2^32 -> 0 <= S < 2^64 ->
  (p + nold <= NEW \/ NEW + n <= p) ->
  rw_cells asegs m 0xa54d8 [C8 (Z_to_bv 64 0xa7358)] ->
  rw_cells asegs m 0xa7358 [C8 (Z_to_bv 64 0x9e6a0); C8 (Z_to_bv 64 0x9ead4)] ->
  rw_cells asegs m (p + -16) [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 nold); C8 (Z_to_bv 64 actx)] ->
  rw_cells asegs m p [CB (Z.to_nat nold) bs] -> length bs = Z.to_nat nold ->
  rw_cells asegs m NEW [CB (Z.to_nat n) uj] -> length uj = Z.to_nat n ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG (p + -16) 16 -> rng RNG p nold -> rng RNG NEW n ->
  evtF asegs RNG (ricptC_post sp gp tp s5 s6 s7 s8 s9 s10 s11 F fc p NEW n nold S bs uj m)
    (MS (mkR (Z_to_bv 64 0x34788) sp gp tp t0 t1 t2 (Z_to_bv 64 S) (Z_to_bv 64 p) (Z_to_bv 64 NEW) a1 a2 a3 a4 a5 a6 a7
              (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 n) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x34788) fc None m (seg_rom asegs)).
Section Zd2.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 0).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 1).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 2).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 3).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 4).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 5).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 6).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 7).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 8).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 9).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 10).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 11).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 12).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 13).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 14).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 15).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 16).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 17).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 18).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 19).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 20).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 21).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 22).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 23).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 24).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 25).
Variable F : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 26).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 27).
Variable m : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 28).
Variable p : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 29).
Variable NEW : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 30).
Variable n : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 31).
Variable nold : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 32).
Variable S : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 33).
Variable b1 : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 34).
Variable actx : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 35).
Variable bs : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 36).
Variable uj : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 37).
#[using="Type"] Lemma ricptC_spec__body : ltac:(let T := type of (fun (h : ricptC_spec__stmt) => h RNG sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p NEW n nold S b1 actx bs uj) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (sp, (gp, (tp, (t0, (t1, (t2, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (p, (NEW, (n, (nold, (S, (b1, (actx, (bs, uj)))))))))))))))))))))))))))))))))))))) as _.
 intros MI NEWR P16 PN NEWN NR NOR SR SEP GOTM REAL HD SRC LBS DST LUJ RIMG RTLS RHD RSRC RDST.
  unfold AINSTANCE in *. unfold ricptC_post. cbv zeta.
  remember (Z.min nold n) as mn eqn:EMN.
  assert (MN : 1 <= mn /\ mn <= nold /\ mn <= n) by (subst mn; clear -NR NOR; lia).
  pose proof (munch_refl [(NEW, NEW + mn)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  step.                                                          (* [comment removed for export] *)
  step. if_cases K0; zify_cond K0. { exfalso. clear -K0 NEWR. lia. }     (* [comment removed for export] *)
  lstep. step. step.                                             (* [comment removed for export] *)
  step. if_lit.                                                  (* [comment removed for export] *)
  step. step. step.                                              (* [comment removed for export] *)
  step. if_lit.                                                  (* [comment removed for export] *)
  lstep. lstep.                                                  (* [comment removed for export] *)
  zstep. zstep. rewrite Z.lor_0_l.                               (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. (if_cases KM; zify_cond KM; [| step]);                  (* [comment removed for export] *)
    setreg 19%Z (Z_to_bv 64 mn) ltac:(f_equal; clear -KM EMN; lia).
  all: step; step; step.                                         (* [comment removed for export] *)
  (* [comment removed for export] *)
  all: remember (Z.to_nat mn) as k1 eqn:EK1; remember (Z.to_nat (n - mn)) as k2 eqn:EK2.
  all: assert (EK1' : Z.of_nat k1 = mn) by (subst k1; apply Z2Nat.id; clear -MN; lia).
  all: assert (EK2' : Z.of_nat k2 = n - mn) by (subst k2; apply Z2Nat.id; clear -MN; lia).
  all: lazymatch type of DST with rw_cells ?segs ?mm ?A [CB ?k ?junk] =>
      apply (rw_cells_split_CB segs mm A [] k junk [] [k1; k2]%nat) in DST;
        [| cbn [sum_nat]; apply Nat2Z.inj; rewrite !Nat2Z.inj_add, EK1', EK2', Z2Nat.id by (clear -NR; lia); cbn; clear; lia];
        cbn [app mk_CB_cells] in DST end.
  all: lazymatch type of DST with rw_cells _ _ _ [?c1; ?c2] => change [c1; c2] with ([c1] ++ [c2]) in DST end.
  all: apply rw_cells_app in DST; destruct DST as [DST1 DST2].
  all: cbn [cells_size csize] in DST2; rewrite Nat.add_0_r, EK1' in DST2.
  all: assert (SRCB : bytes_at asegs m p (firstn k1 bs))
    by (destruct SRC as [[_ B] _]; cbn [cells_bytes cbytes app] in B; rewrite app_nil_r in B;
        rewrite <- (firstn_skipn k1 bs) in B; apply bytes_at_app in B; exact (proj1 B)).
  all: pose proof DST2 as DST2k; box DST2k.
  all: apply (munch_weaken _ [(bv_unsigned (Z_to_bv 64 NEW), bv_unsigned (Z_to_bv 64 NEW) + bv_unsigned (Z_to_bv 64 mn))]%Z) in MU;
    [| rewrite !unsigned_lit by (clear -NEWR NR MN; lia); unfold sub_fp; cbn [outside]; intros q Hq; exact Hq].
  all: step.                                                     (* [comment removed for export] *)
  all: call (memcpy_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (firstn k1 bs) (firstn k1 uj)).
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- mem_inv _ _ => assumption
       | |- bytes_at _ _ _ _ => rewrite unsigned_lit by (clear -P16 PN NOR; lia); exact SRCB
       | |- rw_cells _ _ _ _ => rewrite !unsigned_lit by (clear -NEWR NR MN; lia); rewrite <- EK1; exact DST1
       | |- length _ = _ => rewrite length_firstn, LBS, unsigned_lit by (clear -NR MN; lia); clear -MN EK1 EK1'; lia
       | |- rng _ _ _ => rewrite !unsigned_lit by (clear -NEWR NR P16 PN NOR MN; lia); first [eapply rng_sub'; [exact RSRC|]; clear -MN; lia | eapply rng_sub'; [exact RDST|]; clear -MN; lia]
       | |- _ \/ _ => rewrite !unsigned_lit by (clear -NEWR NR P16 PN NOR MN; lia); clear -SEP MN; lia
       end.
  all: rewrite !unsigned_lit in MU by (clear -NEWR NR MN; lia); rewrite !unsigned_lit in PC by (clear -NEWR NR MN; lia); rewrite <- EK1 in PC.
  all: unbox DST2k.
  all: lazymatch type of MU with munch ?W _ ?m' =>
         apply (rw_cells_transport asegs W m m' _ _) in DST2k;
         [| exact MU | exact WM | cbn [disjoint_from cells_size csize]; rewrite Nat.add_0_r, EK2'; clear -MN; lia] end.
  all: do 6 step.                                                (* [comment removed for export] *)
  all: step.                                                     (* [comment removed for export] *)
  all: apply evtF_done; unfold AINSTANCE; do 10 eexists.
  all: (split; [reflexivity|]); (split; [exact MU|]); (split; [exact WM|]); (split; [assumption|]).
  all: assert (FS : firstn k2 (skipn k1 uj) = skipn k1 uj)
    by (apply firstn_all2; rewrite length_skipn, LUJ; apply Nat2Z.inj_le; rewrite Nat2Z.inj_sub, EK1', EK2', Z2Nat.id by (clear -NR MN EK1'; lia); clear; lia).
  all: rewrite FS in DST2k.
  all: assert (DSTJ : rw_cells asegs _ NEW ([CB k1 (firstn k1 bs)] ++ [CB k2 (skipn k1 uj)]))
    by (apply rw_cells_app; split; [exact PC | cbn [cells_size csize]; rewrite Nat.add_0_r, EK1'; exact DST2k]).
  all: eapply rw_cells_recast; [exact DSTJ | | | ].
  all: try (cbn [cells_size csize app]; rewrite !Nat.add_0_r; apply Nat2Z.inj; rewrite Nat2Z.inj_add, EK1', EK2', Z2Nat.id by (clear -NR; lia); clear; lia).
  all: try (cbn [cells_bytes cbytes app]; rewrite !app_nil_r; reflexivity).
  all: cbn [cells_wf cell_wf]; split; [| exact I]; rewrite length_app, length_firstn, length_skipn, LBS, LUJ;
       apply Nat2Z.inj; rewrite Nat2Z.inj_add, Nat2Z.inj_min, Nat2Z.inj_sub, EK1', !Z2Nat.id by (clear -NR NOR MN EK1'; lia); clear -MN; lia.
Qed.
End Zd2.
#[using="Type"] Lemma ricptC_spec : ltac:(let t := eval cbv delta [ricptC_spec__stmt] in ricptC_spec__stmt in exact t).
Proof. exact ricptC_spec__body. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma ricptD_spec : forall RNG sp gp tp t0 t1 t2 s0x s1x a0 a1 a2 a3 a4 a5 a6 a7 s2x s3x s5x s6x s7 s8 s9 s10 s11 t3 t4 t5 t6
    (rav s0v s1v s2v s3v s4v s5v s6v r4 r3 r2 r1 r0 spv : word) (F : bvmap 5 word) fc (m : amem) (NEW lo : Z) (fr0 junk2 : list byte),
  stk asegs m lo (bv_unsigned sp + -2208) -> ATOP <= lo -> lo <= bv_unsigned sp - 2208 ->
  mem_inv asegs m ->
  0 < NEW < 2^64 ->
  rw_cells asegs m (bv_unsigned sp + -2208) [C8 r4; C8 r3; C8 r2; C8 r1; C8 r0; C8 (Z_to_bv 64 0x3470c)] ->
  rw_cells asegs m (bv_unsigned sp + -2160) [CB 8 fr0; C8 (Z_to_bv 64 0x56960)] ->
  (exists csP, rw_cells asegs m (bv_unsigned sp + -2144) csP /\ cells_size csP = 8%nat) ->
  (exists csA, rw_cells asegs m (bv_unsigned sp + -2136) csA /\ cells_size csA = 16%nat) ->
  (exists csT, rw_cells asegs m (bv_unsigned sp + -2120) csT /\ cells_size csT = 2040%nat) ->
  rw_cells asegs m (bv_unsigned sp + -80) [C8 spv; CB 8 junk2; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (fun ms' => exists a0',
      ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 NEW) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc rav) fc None m (seg_rom asegs)
      /\ a0' = a0 /\ stk asegs m lo (bv_unsigned sp))
    (MS (mkR (Z_to_bv 64 0x3481c) (Z_to_bv 64 (bv_unsigned sp + -2208)) gp tp t0 t1 t2 s0x s1x a0 a1 a2 a3 a4 a5 a6 a7
              s2x s3x (Z_to_bv 64 NEW) s5x s6x s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3481c) fc None m (seg_rom asegs)).
Proof.
  intros until junk2. intros ST CEIL LO MI NEWR FR48 FR16 [csP [FRP SZP]] [csA [FRA SZA]] [csT [FRT SZT]] FRS RIMG RTLS RSTK. atop_facts.
  word_range sp SPR.
  pose proof (munch_refl (@nil (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (rw_cells_forget asegs _ _ _ FRP) as [jP FRP']. rewrite SZP in FRP'. clear FRP.
  pose proof (rw_cells_forget asegs _ _ _ FRA) as [jA FRA']. rewrite SZA in FRA'. clear FRA.
  pose proof (rw_cells_forget asegs _ _ _ FRT) as [jT FRT']. rewrite SZT in FRT'. clear FRT.
  step.                                                          (* [comment removed for export] *)
  do 8 step.                                                     (* [comment removed for export] *)
  step. if_cases K0; zify_cond K0. { exfalso. clear -K0 NEWR. lia. }     (* [comment removed for export] *)
  do 3 step.                                                     (* [comment removed for export] *)
  zstep. do 8 step. zstep. step.                                 (* [comment removed for export] *)
  release_frame FR48 ST (bv_unsigned sp + -2160).
  release_frame FR16 ST (bv_unsigned sp + -2144).
  release_frame FRP' ST (bv_unsigned sp + -2136).
  release_frame FRA' ST (bv_unsigned sp + -2120).
  release_frame FRT' ST (bv_unsigned sp + -80).
  release_frame FRS ST (bv_unsigned sp).
  apply evtF_done. exists a0. split; [reflexivity|]. split; [reflexivity| exact ST].
Qed.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_aintal.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memcpy.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
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


(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition AREALLOC_SYM' : Z := 0x561e8.    (* [comment removed for export] *)
Definition AREALLOC_PC' : Z := 0x56958.     (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ricptA_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (p n lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) m' (junk0 junk1 junk2 : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x5696c) (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2
                  sp (Z_to_bv 64 n)
                  (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 0x56958) sp (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 30) a6 a7
                  (Z_to_bv 64 p) (Z_to_bv 64 0x56958) (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 (bv_unsigned sp + -89))
                  s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x569b0) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2192, bv_unsigned sp); (0xafc00, 0xafc00 + 0x81030); (0x13e488, 0x13e488 + 4)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -2144)
    /\ rw_cells asegs m' (bv_unsigned sp + -2144) [CB 8 junk0]
    /\ rw_cells asegs m' (bv_unsigned sp + -2136) [C8 (Z_to_bv 64 (bv_unsigned sp + -2120)); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]
    /\ rw_cells asegs m' (bv_unsigned sp + -2120) [CB 2040 junk1]
    /\ rw_cells asegs m' (bv_unsigned sp + -80) [C8 sp; CB 8 junk2; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' 0x13e488 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ stk asegs m' 0xafc00 (0xafc00 + 0x81030)
    /\ (forall j, 0 <= j < 32768 -> bytes_at asegs m' (0xafc08 + 8 * j) (le8 (Z_to_bv 64 0))).

Definition ricptA_spec__stmt : Prop := forall (ia : bool) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (p n lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 2192 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 n -> 0 <= p < 2^47 -> 0 <= n < 2^64 ->
  rw_cells asegs m 0xaf6d8 [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m 0xaf6fc [C4 (Z_to_bv 64 30)] ->
  rw_cells asegs m 0xa5880 [C8 (Z_to_bv 64 0x140528); C8 (Z_to_bv 64 0xac1f8); C8 (Z_to_bv 64 0xae9f8);
                             C8 (Z_to_bv 64 0xaf6e8); C8 (Z_to_bv 64 0xaf6f0); C8 (Z_to_bv 64 0xaf6e0)] ->
  rw_cells asegs m 0x14054a [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m 0xa5870 [C8 (Z_to_bv 64 0x13e4a0)] -> rw_cells asegs m 0x13e4a0 [C8 (Z_to_bv 64 4096)] ->
  (* [comment removed for export] *)
  rw_cells asegs m AIA_FLAG [C1 (Z_to_bv 8 (if ia then 1 else 0)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  stk asegs m AIA_BASE (AIA_BASE + AIA_SIZE) ->
  (ia = true -> forall j, 0 <= j < 32768 -> bytes_at asegs m (AIA_MAP1 + 8 * j) (le8 (Z_to_bv 64 0))) ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (ricptA_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc p n lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AREALLOC_SYM') fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable ia : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 5).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 6).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 7).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 8).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 9).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 10).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 11).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 12).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 13).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 14).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 15).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 16).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 17).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 18).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 19).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 20).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 21).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 22).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 23).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 24).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 25).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 26).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 27).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 28).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 29).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 30).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 31).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 32).
Variable F : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 33).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 34).
Variable m : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 35).
Variable p : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 36).
Variable n : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 37).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'ricptA_spec__stmt 38).
#[using="Type"] Lemma ricptA_spec__body : ltac:(let T := type of (fun (h : ricptA_spec__stmt) => h ia RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p n lo) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (ia, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (p, (n, lo))))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO MI -> -> PR NR INI MCS GOT CF34 PG1 PG2 FL IA Z2 RIMG RTLS RSTK. atop_facts.
  unfold AREALLOC_SYM', AIA_BASE, AIA_SIZE, AIA_FLAG, AIA_MAP1, AIA_MAP1_LEN in *.
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 2192, bv_unsigned sp); (0xafc00, 0xafc00 + 0x81030); (0x13e488, 0x13e488 + 4)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  pose proof (munch_refl [(bv_unsigned sp - 2192, bv_unsigned sp)]%Z m) as MU0.
  step.                                                          (* [comment removed for export] *)
  carve_frame 2144%nat ST.
  lazymatch type of FR with rw_cells ?segs ?mm ?A [CB ?n ?junk] =>
    apply (rw_cells_split_CB segs mm A [] n junk [] [8; 16; 2040; 80]%nat) in FR; [| cbn; lia]; cbn [app mk_CB_cells] in FR end.
  (* [comment removed for export] *)
  repeat match type of FR with context [CB _ ?j] => lazymatch j with firstn _ _ => idtac | skipn _ _ => idtac end;
           let x := fresh "jkf" in set (x := j) in FR; clearbody x end.
  rw_split FR 1%nat FRp FR'. rw_split FR' 1%nat FRa FR''. rw_split FR'' 1%nat FRt FRs.
  do 9 step.                                                     (* [comment removed for export] *)
  zstep. zstep. step. step. step.                                (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. carve_frame 16%nat ST.
  do 5 step. lstep. step. step. step. if_lit.                    (* [comment removed for export] *)
  do 4 step. release_frame FR ST (bv_unsigned sp + -2144).
  step. if_lit.                                                  (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (Z2' : ia = true -> forall j, 0 <= j < 32768 -> bytes_at asegs mm (719880 + 8 * j) (le8 (Z_to_bv 64 0)))
      by (intros Hia j Hj; eapply bytes_at_agree; [exact (Z2 Hia j Hj)|];
          intros i Hi; apply MU0; cbn [outside]; rewrite length_le8 in Hi; rewrite wa_unsigned by lia; lia) end.
  clear Z2 MU0.
  step. call_sp internal_allocator_spec;
    [exact ST| exact CEIL| lia| exact MI| exact FL| exact IA| exact Z2'| exact PG1| exact PG2| solve_rng|].
  try rename MI0 into MI. clear Z2'.
  match goal with H : stk asegs ?mm lo _ |- _ => rename H into ST end.
  match goal with H : stk asegs ?mm 719872 _ |- _ => rename H into IA' end.
  match goal with H : rw_cells asegs ?mm 1303688 _ |- _ => rename H into FL' end.
  match goal with H : forall j, _ -> bytes_at asegs _ _ _ |- _ => rename H into MAP end.
  snapshot [(bv_unsigned sp - 2192, bv_unsigned sp)]%Z MU1 WM1.
  (* [comment removed for export] *)
  zstep. setreg 11%Z (Z_to_bv 64 0) ltac:(f_equal; rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; lia).
  step. if_lit.                                (* [comment removed for export] *)
  zstep.                                       (* [comment removed for export] *)
  remember (Z.shiftr p 32) as j eqn:Hj.
  assert (JR : 0 <= j < 32768) by (subst j; rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
  zstep. rewrite (Z.shiftl_mul_pow2 j 3) by lia. change (2^3) with 8. zstep.   (* [comment removed for export] *)
  pose proof (bytes_at_read8 _ _ _ (MAP j JR)) as RD.
  replace (719880 + 8 * j) with (719872 + j * 8 + 8) in RD by lia.
  step. clear RD.                              (* [comment removed for export] *)
  step. step. if_lit.                          (* [comment removed for export] *)
  clear Hj JR.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep. zstep. zstep.   (* [comment removed for export] *)
  step. sstep. step.                                             (* [comment removed for export] *)
  step. step. lstep. step. step.                                 (* [comment removed for export] *)
  step. step. if_lit.                                            (* [comment removed for export] *)
  step. step. step.                                              (* [comment removed for export] *)
  step. step. lstep. step.                                       (* [comment removed for export] *)
  step. step. lstep. step. step.                                 (* [comment removed for export] *)
  step. zstep. zstep. zstep. step.                               (* [comment removed for export] *)
  change ((Z.b2z (30 <? 1) + -1) mod 18446744073709551616) with 18446744073709551615. rewrite land_ones_l by lia.
  sstep.                                                         (* [comment removed for export] *)
  step. if_lit.                                                  (* [comment removed for export] *)
  zstep. zstep. step. step. step. step.                          (* [comment removed for export] *)
  rw_split FRa 1%nat FRa1 FRa2. apply rw_cells_C8_to_C4C4_zero in FRa2. rw_join FRa1 FRa2 FRA.
  apply evtF_done. unfold ricptA_post. do 13 eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
  split; [exact FRp|]. split; [exact FRA|]. split; [exact FRt|]. split; [exact FRs|]. split; [exact FL'|]. split; [exact IA'|].
  intros j0 Hj0. eapply bytes_at_agree; [exact (MAP j0 Hj0)|].
  intros i Hi. apply MU1. cbn [outside]. rewrite length_le8 in Hi. rewrite wa_unsigned by lia. lia.
Qed.
End Zd1.
#[using="Type"] Lemma ricptA_spec : ltac:(let t := eval cbv delta [ricptA_spec__stmt] in ricptA_spec__stmt in exact t).
Proof. exact ricptA_spec__body. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ricptB_post (sp gp tp s3v s4v s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (p n t lo : Z) (t0 t1 t2 a7 t3 t4 t5 t6 : word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists m' (fr0 : list byte) (sj' : list word),
    ms' = MS (mkR (Z_to_bv 64 0x347f0) (Z_to_bv 64 (bv_unsigned sp + -2208)) gp tp t0 t1 t2
                  (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 p)
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 n) (Z_to_bv 64 8) (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 1) (Z_to_bv 64 1)
                  (Z_to_bv 64 (bv_unsigned sp + -2136)) a7
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 n) s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x33c70) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2240, bv_unsigned sp - 2144); (t + 2800, t + 2800 + 368)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -2208)
    /\ rw_cells asegs m' (bv_unsigned sp + -2208) [C8 s4v; C8 s3v; C8 (Z_to_bv 64 p); C8 (Z_to_bv 64 n); C8 sp; C8 (Z_to_bv 64 0x34774)]
    /\ rw_cells asegs m' (bv_unsigned sp + -2160) [CB 8 fr0; C8 (Z_to_bv 64 0x569c8)]
    /\ u64arr asegs m' (t + 2800) sj' /\ length sj' = 46%nat.

#[using="Type"] Lemma ricptB_spec : forall RNG ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (p n ctx t lo : Z) (sj : list word),
  stk asegs m lo (bv_unsigned sp + -2144) -> ATOP <= lo -> lo <= bv_unsigned sp - 2240 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  s1 = Z_to_bv 64 n -> s2 = Z_to_bv 64 p -> 1 <= p < 2^64 -> 1 <= n < 2^64 ->
  rw_cells asegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells asegs m ATSDK [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  0 < ctx -> AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) ->
  (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  evtF asegs RNG (ricptB_post sp gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc p n t lo t0 t1 t2 a7 t3 t4 t5 t6 m)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2 sp s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x569b4) fc None m (seg_rom asegs)).
Proof.
  intros until sj. intros ST CEIL LO MI TP -> -> PR NR TI TK T88 TSD CT CX0 C0 C1 T0 T1 CT2 STATS LSJ RIMG RTLS RSTK RCTX RT.
  pose proof T0 as T0'. unfold iclr, AIMG_LO, AIMG_HI in T0'. atop_facts.
  unfold AIMG_HI, AINSTANCE, ATSDI, ATSDK, ATP88, ATSD in *.
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 2240, bv_unsigned sp - 2144); (t + 2800, t + 2800 + 368)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep. step. step. step.                                (* [comment removed for export] *)
  carve_frame 16%nat ST. rename FR into FR16.
  step. step. step. step.                                        (* [comment removed for export] *)
  step. if_cases K0; zify_cond K0. { exfalso. clear -K0 PR. lia. }       (* [comment removed for export] *)
  step.                                                          (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1. 2: { exfalso. clear -K1 NR. lia. }    (* [comment removed for export] *)
  step. zstep. step. step. step.                                 (* [comment removed for export] *)
  carve_frame 48%nat ST.
  do 7 step.                                                     (* [comment removed for export] *)
  step. if_cases K2; zify_cond K2. { exfalso. clear -K2 PR. lia. }       (* [comment removed for export] *)
  step.                                                          (* [comment removed for export] *)
  step. if_cases K3; zify_cond K3. { exfalso. clear -K3 NR. lia. }       (* [comment removed for export] *)
  step. step. step.                                              (* [comment removed for export] *)
  box RT.
  step. call_sp thread_stats_spec;
    [exact ST| exact CEIL| lia| exact MI| exact TP| exact TI| exact TK| exact T88| exact TSD| exact CT| lia| exact C1| exact T0| exact T1| solve_rng|].
  unbox RT. rename POST into ST. try rename MI0 into MI.
  aload STATS 7 (t + 2800 + 56).                                 (* [comment removed for export] *)
  aload STATS 8 (t + 2800 + 64).                                 (* [comment removed for export] *)
  zstep. zstep.                                                  (* [comment removed for export] *)
  astore STATS 7.                                                (* [comment removed for export] *)
  astore STATS 8.                                                (* [comment removed for export] *)
  do 6 step.                                                     (* [comment removed for export] *)
  step.                                                          (* [comment removed for export] *)
  apply evtF_done. unfold ricptB_post, AINSTANCE. do 3 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|]. split; [exact FR16|].
  split; [exact STATS|]. rewrite !upd_length. exact LSJ.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ricptC_post (sp gp tp s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (p NEW n nold S : Z) (bs uj : list byte) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a6 a7 t3 t4 t5 t6 m',
    let mn := Z.min nold n in
    ms' = MS (mkR (Z_to_bv 64 0x34884) sp gp tp t0 t1 t2
                  (Z_to_bv 64 S) (Z_to_bv 64 p)
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 p) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 S) (Z_to_bv 64 1) a6 a7
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 mn) (Z_to_bv 64 NEW) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x3395c) fc None m' (seg_rom asegs)
    /\ munch [(NEW, NEW + mn)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' NEW [CB (Z.to_nat n) (firstn (Z.to_nat mn) bs ++ skipn (Z.to_nat mn) uj)].

Definition ricptC_spec__stmt : Prop := forall RNG sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (p NEW n nold S b1 actx : Z) (bs uj : list byte),
  mem_inv asegs m ->
  0 < NEW < 2^64 -> 16 <= p -> p + nold < 2^64 -> NEW + n < 2^64 -> 1 <= n < 2^32 -> 1 <= nold < 2^32 -> 0 <= S < 2^64 ->
  (p + nold <= NEW \/ NEW + n <= p) ->
  rw_cells asegs m 0xa58b8 [C8 (Z_to_bv 64 0xa7738)] ->
  rw_cells asegs m 0xa7738 [C8 (Z_to_bv 64 0x9ea84); C8 (Z_to_bv 64 0x9eeb8)] ->
  rw_cells asegs m (p + -16) [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 nold); C8 (Z_to_bv 64 actx)] ->
  rw_cells asegs m p [CB (Z.to_nat nold) bs] -> length bs = Z.to_nat nold ->
  rw_cells asegs m NEW [CB (Z.to_nat n) uj] -> length uj = Z.to_nat n ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG (p + -16) 16 -> rng RNG p nold -> rng RNG NEW n ->
  evtF asegs RNG (ricptC_post sp gp tp s5 s6 s7 s8 s9 s10 s11 F fc p NEW n nold S bs uj m)
    (MS (mkR (Z_to_bv 64 0x347f0) sp gp tp t0 t1 t2 (Z_to_bv 64 S) (Z_to_bv 64 p) (Z_to_bv 64 NEW) a1 a2 a3 a4 a5 a6 a7
              (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 n) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x347f0) fc None m (seg_rom asegs)).
Section Zd2.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 0).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 1).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 2).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 3).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 4).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 5).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 6).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 7).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 8).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 9).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 10).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 11).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 12).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 13).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 14).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 15).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 16).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 17).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 18).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 19).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 20).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 21).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 22).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 23).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 24).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 25).
Variable F : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 26).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 27).
Variable m : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 28).
Variable p : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 29).
Variable NEW : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 30).
Variable n : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 31).
Variable nold : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 32).
Variable S : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 33).
Variable b1 : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 34).
Variable actx : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 35).
Variable bs : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 36).
Variable uj : ltac2:(SecDietF.SzSecF.ty 'ricptC_spec__stmt 37).
#[using="Type"] Lemma ricptC_spec__body : ltac:(let T := type of (fun (h : ricptC_spec__stmt) => h RNG sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p NEW n nold S b1 actx bs uj) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (sp, (gp, (tp, (t0, (t1, (t2, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (p, (NEW, (n, (nold, (S, (b1, (actx, (bs, uj)))))))))))))))))))))))))))))))))))))) as _.
 intros MI NEWR P16 PN NEWN NR NOR SR SEP GOTM REAL HD SRC LBS DST LUJ RIMG RTLS RHD RSRC RDST.
  unfold AINSTANCE in *. unfold ricptC_post. cbv zeta.
  remember (Z.min nold n) as mn eqn:EMN.
  assert (MN : 1 <= mn /\ mn <= nold /\ mn <= n) by (subst mn; clear -NR NOR; lia).
  pose proof (munch_refl [(NEW, NEW + mn)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  step.                                                          (* [comment removed for export] *)
  step. if_cases K0; zify_cond K0. { exfalso. clear -K0 NEWR. lia. }     (* [comment removed for export] *)
  lstep. step. step.                                             (* [comment removed for export] *)
  step. if_lit.                                                  (* [comment removed for export] *)
  step. step. step.                                              (* [comment removed for export] *)
  step. if_lit.                                                  (* [comment removed for export] *)
  lstep. lstep.                                                  (* [comment removed for export] *)
  zstep. zstep. rewrite Z.lor_0_l.                               (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. (if_cases KM; zify_cond KM; [| step]);                  (* [comment removed for export] *)
    setreg 19%Z (Z_to_bv 64 mn) ltac:(f_equal; clear -KM EMN; lia).
  all: step; step; step.                                         (* [comment removed for export] *)
  (* [comment removed for export] *)
  all: remember (Z.to_nat mn) as k1 eqn:EK1; remember (Z.to_nat (n - mn)) as k2 eqn:EK2.
  all: assert (EK1' : Z.of_nat k1 = mn) by (subst k1; apply Z2Nat.id; clear -MN; lia).
  all: assert (EK2' : Z.of_nat k2 = n - mn) by (subst k2; apply Z2Nat.id; clear -MN; lia).
  all: lazymatch type of DST with rw_cells ?segs ?mm ?A [CB ?k ?junk] =>
      apply (rw_cells_split_CB segs mm A [] k junk [] [k1; k2]%nat) in DST;
        [| cbn [sum_nat]; apply Nat2Z.inj; rewrite !Nat2Z.inj_add, EK1', EK2', Z2Nat.id by (clear -NR; lia); cbn; clear; lia];
        cbn [app mk_CB_cells] in DST end.
  all: lazymatch type of DST with rw_cells _ _ _ [?c1; ?c2] => change [c1; c2] with ([c1] ++ [c2]) in DST end.
  all: apply rw_cells_app in DST; destruct DST as [DST1 DST2].
  all: cbn [cells_size csize] in DST2; rewrite Nat.add_0_r, EK1' in DST2.
  all: assert (SRCB : bytes_at asegs m p (firstn k1 bs))
    by (destruct SRC as [[_ B] _]; cbn [cells_bytes cbytes app] in B; rewrite app_nil_r in B;
        rewrite <- (firstn_skipn k1 bs) in B; apply bytes_at_app in B; exact (proj1 B)).
  all: pose proof DST2 as DST2k; box DST2k.
  all: apply (munch_weaken _ [(bv_unsigned (Z_to_bv 64 NEW), bv_unsigned (Z_to_bv 64 NEW) + bv_unsigned (Z_to_bv 64 mn))]%Z) in MU;
    [| rewrite !unsigned_lit by (clear -NEWR NR MN; lia); unfold sub_fp; cbn [outside]; intros q Hq; exact Hq].
  all: step.                                                     (* [comment removed for export] *)
  all: call (memcpy_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (firstn k1 bs) (firstn k1 uj)).
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- mem_inv _ _ => assumption
       | |- bytes_at _ _ _ _ => rewrite unsigned_lit by (clear -P16 PN NOR; lia); exact SRCB
       | |- rw_cells _ _ _ _ => rewrite !unsigned_lit by (clear -NEWR NR MN; lia); rewrite <- EK1; exact DST1
       | |- length _ = _ => rewrite length_firstn, LBS, unsigned_lit by (clear -NR MN; lia); clear -MN EK1 EK1'; lia
       | |- rng _ _ _ => rewrite !unsigned_lit by (clear -NEWR NR P16 PN NOR MN; lia); first [eapply rng_sub'; [exact RSRC|]; clear -MN; lia | eapply rng_sub'; [exact RDST|]; clear -MN; lia]
       | |- _ \/ _ => rewrite !unsigned_lit by (clear -NEWR NR P16 PN NOR MN; lia); clear -SEP MN; lia
       end.
  all: rewrite !unsigned_lit in MU by (clear -NEWR NR MN; lia); rewrite !unsigned_lit in PC by (clear -NEWR NR MN; lia); rewrite <- EK1 in PC.
  all: unbox DST2k.
  all: lazymatch type of MU with munch ?W _ ?m' =>
         apply (rw_cells_transport asegs W m m' _ _) in DST2k;
         [| exact MU | exact WM | cbn [disjoint_from cells_size csize]; rewrite Nat.add_0_r, EK2'; clear -MN; lia] end.
  all: do 6 step.                                                (* [comment removed for export] *)
  all: step.                                                     (* [comment removed for export] *)
  all: apply evtF_done; unfold AINSTANCE; do 10 eexists.
  all: (split; [reflexivity|]); (split; [exact MU|]); (split; [exact WM|]); (split; [assumption|]).
  all: assert (FS : firstn k2 (skipn k1 uj) = skipn k1 uj)
    by (apply firstn_all2; rewrite length_skipn, LUJ; apply Nat2Z.inj_le; rewrite Nat2Z.inj_sub, EK1', EK2', Z2Nat.id by (clear -NR MN EK1'; lia); clear; lia).
  all: rewrite FS in DST2k.
  all: assert (DSTJ : rw_cells asegs _ NEW ([CB k1 (firstn k1 bs)] ++ [CB k2 (skipn k1 uj)]))
    by (apply rw_cells_app; split; [exact PC | cbn [cells_size csize]; rewrite Nat.add_0_r, EK1'; exact DST2k]).
  all: eapply rw_cells_recast; [exact DSTJ | | | ].
  all: try (cbn [cells_size csize app]; rewrite !Nat.add_0_r; apply Nat2Z.inj; rewrite Nat2Z.inj_add, EK1', EK2', Z2Nat.id by (clear -NR; lia); clear; lia).
  all: try (cbn [cells_bytes cbytes app]; rewrite !app_nil_r; reflexivity).
  all: cbn [cells_wf cell_wf]; split; [| exact I]; rewrite length_app, length_firstn, length_skipn, LBS, LUJ;
       apply Nat2Z.inj; rewrite Nat2Z.inj_add, Nat2Z.inj_min, Nat2Z.inj_sub, EK1', !Z2Nat.id by (clear -NR NOR MN EK1'; lia); clear -MN; lia.
Qed.
End Zd2.
#[using="Type"] Lemma ricptC_spec : ltac:(let t := eval cbv delta [ricptC_spec__stmt] in ricptC_spec__stmt in exact t).
Proof. exact ricptC_spec__body. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma ricptD_spec : forall RNG sp gp tp t0 t1 t2 s0x s1x a0 a1 a2 a3 a4 a5 a6 a7 s2x s3x s5x s6x s7 s8 s9 s10 s11 t3 t4 t5 t6
    (rav s0v s1v s2v s3v s4v s5v s6v r4 r3 r2 r1 r0 spv : word) (F : bvmap 5 word) fc (m : amem) (NEW lo : Z) (fr0 junk2 : list byte),
  stk asegs m lo (bv_unsigned sp + -2208) -> ATOP <= lo -> lo <= bv_unsigned sp - 2208 ->
  mem_inv asegs m ->
  0 < NEW < 2^64 ->
  rw_cells asegs m (bv_unsigned sp + -2208) [C8 r4; C8 r3; C8 r2; C8 r1; C8 r0; C8 (Z_to_bv 64 0x34774)] ->
  rw_cells asegs m (bv_unsigned sp + -2160) [CB 8 fr0; C8 (Z_to_bv 64 0x569c8)] ->
  (exists csP, rw_cells asegs m (bv_unsigned sp + -2144) csP /\ cells_size csP = 8%nat) ->
  (exists csA, rw_cells asegs m (bv_unsigned sp + -2136) csA /\ cells_size csA = 16%nat) ->
  (exists csT, rw_cells asegs m (bv_unsigned sp + -2120) csT /\ cells_size csT = 2040%nat) ->
  rw_cells asegs m (bv_unsigned sp + -80) [C8 spv; CB 8 junk2; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (fun ms' => exists a0',
      ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 NEW) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc rav) fc None m (seg_rom asegs)
      /\ a0' = a0 /\ stk asegs m lo (bv_unsigned sp))
    (MS (mkR (Z_to_bv 64 0x34884) (Z_to_bv 64 (bv_unsigned sp + -2208)) gp tp t0 t1 t2 s0x s1x a0 a1 a2 a3 a4 a5 a6 a7
              s2x s3x (Z_to_bv 64 NEW) s5x s6x s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x34884) fc None m (seg_rom asegs)).
Proof.
  intros until junk2. intros ST CEIL LO MI NEWR FR48 FR16 [csP [FRP SZP]] [csA [FRA SZA]] [csT [FRT SZT]] FRS RIMG RTLS RSTK. atop_facts.
  word_range sp SPR.
  pose proof (munch_refl (@nil (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (rw_cells_forget asegs _ _ _ FRP) as [jP FRP']. rewrite SZP in FRP'. clear FRP.
  pose proof (rw_cells_forget asegs _ _ _ FRA) as [jA FRA']. rewrite SZA in FRA'. clear FRA.
  pose proof (rw_cells_forget asegs _ _ _ FRT) as [jT FRT']. rewrite SZT in FRT'. clear FRT.
  step.                                                          (* [comment removed for export] *)
  do 8 step.                                                     (* [comment removed for export] *)
  step. if_cases K0; zify_cond K0. { exfalso. clear -K0 NEWR. lia. }     (* [comment removed for export] *)
  do 3 step.                                                     (* [comment removed for export] *)
  zstep. do 8 step. zstep. step.                                 (* [comment removed for export] *)
  release_frame FR48 ST (bv_unsigned sp + -2160).
  release_frame FR16 ST (bv_unsigned sp + -2144).
  release_frame FRP' ST (bv_unsigned sp + -2136).
  release_frame FRA' ST (bv_unsigned sp + -2120).
  release_frame FRT' ST (bv_unsigned sp + -80).
  release_frame FRS ST (bv_unsigned sp).
  apply evtF_done. exists a0. split; [reflexivity|]. split; [reflexivity| exact ST].
Qed.
End CANSEC1.
End TwB.
End F_arealloc_iseg.

(* [comment removed for export] *)
Module F_acalloc_pre.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecSlog__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc1b__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aunwind. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_acalloc_iseg__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc1b__A3W.F_aalloc1b OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1b0 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aunwind OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc1b__A3W.F_aunwind2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc__A3W.F_amalloc_icpt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_iseg__A3W.F_acalloc_iseg.
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


(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition calloc_pre_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (nm sz n t lo : Z) (trc : list Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (spA : word) t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 (s4A s5A s6A s3i : word) (fr0 frc junk0 junk2 : list byte) (tb : list word) m',
    ms' = MS (mkR (Z_to_bv 64 0x33ea8) (Z_to_bv 64 (bv_unsigned spA + -128)) gp tp t0 t1 t2
                  (Z_to_bv 64 1) (Z_to_bv 64 n)
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 (t + 208)) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 8) a4 a5 a6 a7
                  (Z_to_bv 64 8) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n)
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 t) (Z_to_bv 64 1)
                  t3 t4 t5 t6)
             F (Z_to_bv 64 0x38388) fc None m' (seg_rom asegs)
    /\ bv_unsigned spA = bv_unsigned sp - 2192
    /\ munch [(bv_unsigned sp - 2368, bv_unsigned sp); (t + 3168, t + 3169)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp - 2320)
    /\ rw_cells asegs m' (bv_unsigned sp - 2320)
         [CB 8 fr0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 16); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6A; C8 s5A;
          C8 s4A; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 AINSTANCE); C8 (Z_to_bv 64 (bv_unsigned sp + -2136)); C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 0x345e4)]
    /\ rw_cells asegs m' (bv_unsigned sp + -2192) [CB 8 frc; C8 s3i; C8 (Z_to_bv 64 nm); C8 (Z_to_bv 64 sz); C8 sp; C8 (Z_to_bv 64 0x566c0)]
    /\ rw_cells asegs m' (bv_unsigned sp + -2144) [CB 8 junk0]
    /\ rw_cells asegs m' (bv_unsigned sp + -2136) [C8 (Z_to_bv 64 (bv_unsigned sp + -2136 + 16)); C8 (Z_to_bv 64 (1 + Z.of_nat (length trc)))]
    /\ u64arr asegs m' (bv_unsigned sp + -2136 + 16) tb /\ length tb = 255%nat
    /\ map bv_unsigned (firstn (Datatypes.S (length trc)) tb) = ACALLOC_PC :: trc
    /\ rw_cells asegs m' (bv_unsigned sp + -80) [C8 sp; CB 8 junk2; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' (t + 3168) [C1 (Z_to_bv 8 0)].

Definition calloc_pre_spec__stmt : Prop := forall (L : alayout) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (nm sz n t lo top bot : Z) (tr trc : list Z),
  let ctx := al_ctx L in
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 nm -> a1 = Z_to_bv 64 sz -> 1 <= nm -> 1 <= sz -> n = nm * sz -> 1 <= n -> is_primary n = true ->
  bv_unsigned sp mod 16 = 0 ->
  (* [comment removed for export] *)
  allocA_cells m ctx t -> poison_cells m ->
  rw_cells asegs m 0xaf2fc [C4 (Z_to_bv 64 30)] ->
  rw_cells asegs m 0x14014a [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m GOT_PGSZ [C8 (Z_to_bv 64 APGSZ)] -> rw_cells asegs m APGSZ [C8 (Z_to_bv 64 4096)] ->
  (* [comment removed for export] *)
  rw_cells asegs m (ctx + 8) [C4 (Z_to_bv 64 0)] -> rw_cells asegs m t [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (t + 8) [C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)] ->
  rw_cells asegs m (t + 40) [C1 (Z_to_bv 8 0)] -> rw_cells asegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> sclr ctx 65536 ->
  iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> t mod 4096 = 0 -> sclr t 4096 ->
  (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  (* [comment removed for export] *)
  (bv_unsigned sp + 16 < top /\ uchain m top ACALLOC_PC (bv_unsigned sp) (bv_unsigned s0) 28%nat tr /\ (length tr <= 28)%nat /\ trc = bv_unsigned ra :: tr
   /\ rng RNG lo (top - lo))
  \/ (top <= bv_unsigned sp + 16 /\ bv_unsigned sp < 2^47 /\ trc = []) ->
  bv_unsigned s0 <> bv_unsigned sp + 8 ->
  0 <= bot -> bot < bv_unsigned sp -> bot + 4096 <= top -> top <= 2^47 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> ACALLOC_PC ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  evtF asegs RNG (calloc_pre_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc nm sz n t lo trc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ACALLOC_SYM) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 5).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 6).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 7).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 8).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 9).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 10).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 11).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 12).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 13).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 14).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 15).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 16).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 17).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 18).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 19).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 20).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 21).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 22).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 23).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 24).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 25).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 26).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 27).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 28).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 29).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 30).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 31).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 32).
Variable F : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 33).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 34).
Variable m : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 35).
Variable nm : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 36).
Variable sz : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 37).
Variable n : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 38).
Variable t : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 39).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 40).
Variable top : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 41).
Variable bot : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 42).
Variable tr : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 43).
Variable trc : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 44).
#[using="Type"] Lemma calloc_pre_spec__body : ltac:(let T := type of (fun (h : calloc_pre_spec__stmt) => h L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m nm sz n t lo top bot tr trc) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (nm, (sz, (n, (t, (lo, (top, (bot, (tr, trc))))))))))))))))))))))))))))))))))))))))))))) as _.
 cbv zeta.
  intros ST CEIL LO MI TP Ha0 Ha1 NM1 SZ1 EN N PRIM SP16 AC PC LS1 CT8 GPG PGC CX8 TT0 TT SW UW CX0 CX1 CXS T0 T1 TAL TS CT2
         ARM S0NE B0 BB BTOP TOP RA4 RANE RIMG RTLS RSTK RCTX RT. band_lin.   (* [comment removed for export] *)
  assert (LTRC : (length trc <= 29)%nat) by (destruct ARM as [(_ & _ & L1 & -> & _)|(_ & _ & ->)]; cbn [length]; lia).
  assert (SP47 : bv_unsigned sp < 2^47) by (destruct ARM as [(X1 & _)|(_ & X2 & _)]; lia).
  pose proof AC as AC'. (nd_pre AC' 8%nat; intros INI RSS IMAX TI TK T88 TSD CT; nd_post).
  unfold AIMG_HI, AINSTANCE, ATP88, ATSD, ATSDI, ATSDK, AINITED, ARSSLIM, GOT_PGSZ, APGSZ, ACALLOC_PC in *.
  word_range sp SPR. word_range s0 S0R. word_range ra RAR.
  (pose proof (prim_facts n N PRIM) as ndP__; nd_pre ndP__ 8%nat; intros NS RZR RZE RZM RLR RSR RSM NSR; nd_post).
  assert (OV : nm * sz < 2^64) by (rewrite <- EN; clear -NS RZR RZE RZM RLR RSR RSM NSR N; lia).
  box CT2.
  (nd_pre PC 7%nat; intros GOT GOT80 REAL PC4 PC5 PC6 PC7; nd_post).
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (cicptA_spec RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m nm sz lo);
      try eassumption; try (clear -NM1 SZ1 OV LO; nia); try lia; try solve_rng. }
  cbv beta. intros ms1 PA. unfold cicptA_post in PA.
  (nd_pre PA 14%nat; intros t0a t1a t2a a6a a7a t3a t4a t5a t6a m1 junk0 junk1 junk2 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 8%nat; intros MUa WMa MIa STa FRP FRA FRt FRs; nd_post).
  (* [comment removed for export] *)
  pose proof FRs as FRs0. rw_split FRs0 8%nat FRsx FRsr. clear FRsx.
  destruct FRsr as [[_ BSR] _]. cbn [cells_bytes cbytes app] in BSR. rewrite app_nil_r in BSR.
  apply bytes_at_app in BSR. destruct BSR as [BS0 BRA]. rewrite length_le8 in BRA.
  replace (bv_unsigned sp + -16 + Z.of_nat 8) with (bv_unsigned sp - 8) in BRA by lia.
  replace (bv_unsigned sp + -16) with (bv_unsigned sp - 16) in BS0 by lia.
  (* [comment removed for export] *)
  xport TI MUa WMa ltac:(lia). xport TK MUa WMa ltac:(lia). xport T88 MUa WMa ltac:(lia). xport TSD MUa WMa ltac:(lia).
  xport CT MUa WMa ltac:(lia). xport GPG MUa WMa ltac:(lia). xport PGC MUa WMa ltac:(lia). xport TT MUa WMa ltac:(lia).
  xport SW MUa WMa ltac:(lia). xport UW MUa WMa ltac:(lia). xport INI MUa WMa ltac:(lia).
  pose proof FRA as FRA0. rw_split FRA0 1%nat FRp FRz. rw_split FRz 1%nat SZC TAG.
  change 2040%nat with (8 * 255)%nat in FRt. destruct (u64arr_of_CB _ _ 255%nat _ FRt) as [TB LTB].
  pose proof FRs as FRs1. rw_split FRs1 1%nat BPJ REST.
  replace (bv_unsigned sp + -2128) with (bv_unsigned sp - 2136 + 8) in SZC by lia.
  replace (bv_unsigned sp + -2120) with (bv_unsigned sp - 2136 + 16) in TB by lia.
  replace (bv_unsigned sp + -80) with (bv_unsigned sp - 2136 + 2056) in BPJ by lia.
  (* [comment removed for export] *)
  step.                                                          (* [comment removed for export] *)
  name_sp sp (-2144).
  eapply evtF_cut with (P := unwind_impl_post (bv_unsigned sp - 2136) 353872 (bv_unsigned sp) t _ _ gp tp _ _ _ _ _ _ _ s7 s8 s9 s10 s11 F fc lo trc m1).
  { destruct ARM as [(BT & UC & LTR & Etrc & RTOP)|(BT & BT2 & Etrc)]; rewrite Etrc.
    - (* [comment removed for export] *)
      assert (UC1 : uchain m1 top 353872 bot (bv_unsigned sp) 29%nat ([bv_unsigned ra] ++ tr)).
      { replace ([bv_unsigned ra] ++ tr) with ((if bv_unsigned ra =? 353872 then [] else [bv_unsigned ra]) ++ tr)
          by (replace (bv_unsigned ra =? 353872) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
        eapply (uc_step m1 top 353872 bot (bv_unsigned sp) 29%nat (bv_unsigned s0) (bv_unsigned ra) tr); try lia.
        - rewrite Z_to_bv_bv_unsigned. exact BS0.
        - rewrite Z_to_bv_bv_unsigned. exact BRA.
        - replace (bv_unsigned ra =? 353872) with false by (symmetry; apply Z.eqb_neq; lia). cbn [Nat.pred].
          destruct (Z_le_gt_dec (bv_unsigned sp + 16) (bv_unsigned s0)) as [GE|LT].
          + eapply uchain_frame; [exact UC|]. intros a Ha. apply MUa. cbn [outside]. rewrite unsigned_lit by lia. split; [lia| exact I].
          + inversion UC; subst; [apply uc_stop; assumption | exfalso | exfalso]; Z.div_mod_to_equations; lia. }
      clear BS0 BRA UC.
      change (bv_unsigned ra :: tr) with ([bv_unsigned ra] ++ tr).
    eapply (unwind_impl_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (bv_unsigned sp - 2136) 353872 (bv_unsigned sp) (al_ctx L) t top bot lo (words_of_bytes junk1) ([bv_unsigned ra] ++ tr)).
        all: try lazymatch goal with
             | |- stk _ _ _ _ => rewrite Hsp; exact STa
             | |- mem_inv _ _ => exact MIa
             | |- @eq word _ _ => first [reflexivity | exact TP | rewrite Z_to_bv_bv_unsigned; reflexivity | apply Z_to_bv_eqm; rewrite ?unsigned_lit by lia; lia]
             | |- ex _ => first [eexists; exact SZC | eexists; exact BPJ]
             | |- u64arr _ _ _ _ => exact TB
             | |- uchain _ _ _ _ _ _ _ => exact UC1
             | |- _ \/ _ => unboxed CT2
             | |- rng _ _ _ => solve_rng
             | |- rw_cells _ _ (_ + 152) _ => exact CT
             | |- rw_cells _ _ (_ + 8) [C8 _; C8 _] => exact TT
             | |- rw_cells _ _ (_ + 40) _ => exact SW
             | |- rw_cells _ _ (_ + 3168) _ => exact UW
             end.
        all: try eassumption. all: try (unfold AIMG_HI; lia). all: try (Z.div_mod_to_equations; lia).
        all: match goal with |- ?G => idtac "REMU" G end.
    - (* [comment removed for export] *)
      clear BS0 BRA.
    eapply (unwind_impl_spec0 RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (bv_unsigned sp - 2136) 353872 (bv_unsigned sp) (al_ctx L) t top bot lo (words_of_bytes junk1)).
        all: try lazymatch goal with
             | |- stk _ _ _ _ => rewrite Hsp; exact STa
             | |- mem_inv _ _ => exact MIa
             | |- @eq word _ _ => first [reflexivity | exact TP | rewrite Z_to_bv_bv_unsigned; reflexivity | apply Z_to_bv_eqm; rewrite ?unsigned_lit by lia; lia]
             | |- ex _ => first [eexists; exact SZC | eexists; exact BPJ]
             | |- u64arr _ _ _ _ => exact TB
             | |- uchain _ _ _ _ _ _ _ => exact UC1
             | |- _ \/ _ => unboxed CT2
             | |- rng _ _ _ => solve_rng
             | |- rw_cells _ _ (_ + 152) _ => exact CT
             | |- rw_cells _ _ (_ + 8) [C8 _; C8 _] => exact TT
             | |- rw_cells _ _ (_ + 40) _ => exact SW
             | |- rw_cells _ _ (_ + 3168) _ => exact UW
             end.
        all: try eassumption. all: try (unfold AIMG_HI; lia). all: try (Z.div_mod_to_equations; lia).
        all: match goal with |- ?G => idtac "REMU" G end. }

  cbv beta. intros ms2 PU. unfold unwind_impl_post in PU.
  (nd_pre PU 18%nat; intros t0b t1b t2b a0b a1b a2b a3b a4b a5b a6b a7b t3b t4b t5b t6b m2 tb2 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 10%nat; intros MUu WMu MIu STu SZ2 TB2 LTB2 TRF2 BP2 UW2; nd_post).
  unname_sp. rewrite ?unsigned_lit in MUu by lia. rewrite ?unsigned_lit in STu by lia.
  replace (ret_pc (Z_to_bv 64 353964)) with (Z_to_bv 64 353964) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (cicptB_spec RNG) with (nm := nm) (sz := sz); [exact STu | atop_facts; lia | lia | exact MIu | reflexivity | reflexivity | exact NM1 | exact SZ1 | exact OV | exact RIMG | exact RTLS | solve_rng]. }
  cbv beta. intros ms3 PB. unfold cicptB_post in PB. (nd_pre PB 3%nat; intros m3 frc ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 5%nat; intros MUb WMb MIb STb FR16; nd_post). rewrite <- EN in *.
  (* [comment removed for export] *)
  assert (MU3 : munch [(bv_unsigned sp - 2336, bv_unsigned sp); (t + 3168, t + 3169)]%Z m m3).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUb]]. eapply munch_trans; [| eapply munch_weaken; [| exact MUu]].
    eapply munch_weaken; [| exact MUa]. all: unfold sub_fp; cbn [outside]; intros q Hq; lia. }
  assert (WM3 : wmono asegs m m3). { eapply wmono_trans; [| exact WMb]. eapply wmono_trans; [exact WMa | exact WMu]. }
  assert (MU13 : munch [(bv_unsigned sp - 2336, bv_unsigned sp - 2144); (bv_unsigned sp - 2128, bv_unsigned sp - 2124); (bv_unsigned sp - 2120, bv_unsigned sp - 72); (t + 3168, t + 3169)]%Z m1 m3).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUb]]. eapply munch_weaken; [| exact MUu].
    all: unfold sub_fp; cbn [outside]; intros q Hq; lia. }
  assert (WM13 : wmono asegs m1 m3). { eapply wmono_trans; [exact WMu | exact WMb]. }
  xport INI MU13 WM13 ltac:(lia). xport TI MU13 WM13 ltac:(lia). xport TK MU13 WM13 ltac:(lia). xport T88 MU13 WM13 ltac:(lia).
  xport TSD MU13 WM13 ltac:(lia). xport CT MU13 WM13 ltac:(ub CT2; lia). xport FRp MU13 WM13 ltac:(lia). xport TAG MU13 WM13 ltac:(lia). xport FRP MU13 WM13 ltac:(lia).
  xport REST MU13 WM13 ltac:(lia).
  xport RSS MU3 WM3 ltac:(lia). xport IMAX MU3 WM3 ltac:(lia).
  (* [comment removed for export] *)
  xport SZ2 MUb WMb ltac:(lia). replace (bv_unsigned sp - 2136 + 8) with (bv_unsigned sp + -2128) in SZ2 by lia.
  rw_join SZ2 TAG SZT. apply rw_cells_C4C4_to_C8 in SZT. 2: { cbn [length app]; clear -LTRC; lia. }
  rw_join FRp SZT SS.
  xport TB2 MUb WMb ltac:(rewrite LTB2; lia). xport BP2 MUb WMb ltac:(lia). xport UW2 MUb WMb ltac:(lia).
  rewrite Z_to_bv_bv_unsigned in BP2. rw_join BP2 REST FRS.
  replace (bv_unsigned sp - 2136 + 2056) with (bv_unsigned sp + -80) in FRS by lia.
  (* [comment removed for export] *)
  name_sp sp (-2192).
  step.                                                          (* [comment removed for export] *)
  eapply evtF_mono.
  { eapply (allocA_pre_spec0 RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m3 n (bv_unsigned sp + -2136) (al_ctx L) t lo).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => rewrite Hsp; exact STb
         | |- mem_inv _ _ => exact MIb
         | |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => assumption | |- _ /\ _ => split end)
         | |- @eq word _ _ => first [reflexivity | exact TP]
         | |- _ \/ _ => unboxed CT2
         end.
    all: try lazymatch goal with |- rng _ _ _ => solve_rng end.
    all: try eassumption. all: try (unfold AIMG_HI; lia).
    all: match goal with |- ?G => idtac "REMAL" G end. }
  cbv beta. intros ms4 PL. unfold allocA_pre_post0 in PL.
  (nd_pre PL 13%nat; intros t0c t1c t2c a4c a5c a6c a7c t3c t4c t5c t6c m4 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 5%nat; intros MUl WMl MIl STl [fr0 FRa]; nd_post).
  rewrite ?Hsp in MUl. rewrite ?Hsp in STl. rewrite ?Hsp in FRa.
  xport FR16 MUl WMl ltac:(lia). xport FRP MUl WMl ltac:(lia). xport SS MUl WMl ltac:(lia). xport UW2 MUl WMl ltac:(lia). xport FRS MUl WMl ltac:(lia).
  xport TB2 MUl WMl ltac:(rewrite LTB2; lia).
  unfold calloc_pre_post. lazymatch type of Hsp with bv_unsigned ?spx = _ => exists spx end. do 11 eexists. do 4 eexists. exists fr0, frc, junk0, junk2, tb2, m4.
  split; [reflexivity|]. split; [clear -Hsp; lia|].
  split.
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUl]]. eapply munch_weaken; [| exact MU3].
    all: unfold sub_fp; cbn [outside]; intros q Hq; lia. }
  split; [eapply wmono_trans; [exact WM3 | exact WMl]|]. split; [exact MIl|].
  split; [replace (bv_unsigned sp - 2320) with (bv_unsigned sp + -2192 - 128) by lia; exact STl|].
  split; [replace (bv_unsigned sp - 2320) with (bv_unsigned sp + -2192 - 128) by lia; exact FRa|].
  split; [exact FR16|]. split; [exact FRP|].
  replace (bv_unsigned sp + -2120) with (bv_unsigned sp + -2136 + 16) in SS by lia.
  replace (bv_unsigned sp - 2136 + 16) with (bv_unsigned sp + -2136 + 16) in TB2 by lia.
  split; [exact SS|]. split; [exact TB2|]. split; [exact LTB2|]. split; [exact TRF2|]. split; [exact FRS|]. exact UW2.
  Unshelve. all: try exact STb; try exact STa; try exact STu.
Qed.
End Zd1.
#[using="Type"] Lemma calloc_pre_spec : ltac:(let t := eval cbv delta [calloc_pre_spec__stmt] in calloc_pre_spec__stmt in exact t).
Proof. exact calloc_pre_spec__body. Qed.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc1b__A3W.F_aalloc1b.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1b0.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aunwind.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc1b__A3W.F_aunwind2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc__A3W.F_amalloc_icpt.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_iseg__A3W.F_acalloc_iseg.TwB.
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


(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition calloc_pre_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (nm sz n t lo : Z) (trc : list Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (spA : word) t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 (s4A s5A s6A s3i : word) (fr0 frc junk0 junk2 : list byte) (tb : list word) m',
    ms' = MS (mkR (Z_to_bv 64 0x33f10) (Z_to_bv 64 (bv_unsigned spA + -128)) gp tp t0 t1 t2
                  (Z_to_bv 64 1) (Z_to_bv 64 n)
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 (t + 208)) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 8) a4 a5 a6 a7
                  (Z_to_bv 64 8) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n)
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 t) (Z_to_bv 64 1)
                  t3 t4 t5 t6)
             F (Z_to_bv 64 0x383f0) fc None m' (seg_rom asegs)
    /\ bv_unsigned spA = bv_unsigned sp - 2192
    /\ munch [(bv_unsigned sp - 2368, bv_unsigned sp); (t + 3168, t + 3169)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp - 2320)
    /\ rw_cells asegs m' (bv_unsigned sp - 2320)
         [CB 8 fr0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 16); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6A; C8 s5A;
          C8 s4A; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 AINSTANCE); C8 (Z_to_bv 64 (bv_unsigned sp + -2136)); C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 0x3464c)]
    /\ rw_cells asegs m' (bv_unsigned sp + -2192) [CB 8 frc; C8 s3i; C8 (Z_to_bv 64 nm); C8 (Z_to_bv 64 sz); C8 sp; C8 (Z_to_bv 64 0x56728)]
    /\ rw_cells asegs m' (bv_unsigned sp + -2144) [CB 8 junk0]
    /\ rw_cells asegs m' (bv_unsigned sp + -2136) [C8 (Z_to_bv 64 (bv_unsigned sp + -2136 + 16)); C8 (Z_to_bv 64 (1 + Z.of_nat (length trc)))]
    /\ u64arr asegs m' (bv_unsigned sp + -2136 + 16) tb /\ length tb = 255%nat
    /\ map bv_unsigned (firstn (Datatypes.S (length trc)) tb) = ACALLOC_PC :: trc
    /\ rw_cells asegs m' (bv_unsigned sp + -80) [C8 sp; CB 8 junk2; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' (t + 3168) [C1 (Z_to_bv 8 0)].

Definition calloc_pre_spec__stmt : Prop := forall (L : alayout) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (nm sz n t lo top bot : Z) (tr trc : list Z),
  let ctx := al_ctx L in
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 nm -> a1 = Z_to_bv 64 sz -> 1 <= nm -> 1 <= sz -> n = nm * sz -> 1 <= n -> is_primary n = true ->
  bv_unsigned sp mod 16 = 0 ->
  (* [comment removed for export] *)
  allocA_cells m ctx t -> poison_cells m ->
  rw_cells asegs m 0xaf6fc [C4 (Z_to_bv 64 30)] ->
  rw_cells asegs m 0x14054a [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m GOT_PGSZ [C8 (Z_to_bv 64 APGSZ)] -> rw_cells asegs m APGSZ [C8 (Z_to_bv 64 4096)] ->
  (* [comment removed for export] *)
  rw_cells asegs m (ctx + 8) [C4 (Z_to_bv 64 0)] -> rw_cells asegs m t [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (t + 8) [C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)] ->
  rw_cells asegs m (t + 40) [C1 (Z_to_bv 8 0)] -> rw_cells asegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> sclr ctx 65536 ->
  iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> t mod 4096 = 0 -> sclr t 4096 ->
  (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  (* [comment removed for export] *)
  (bv_unsigned sp + 16 < top /\ uchain m top ACALLOC_PC (bv_unsigned sp) (bv_unsigned s0) 28%nat tr /\ (length tr <= 28)%nat /\ trc = bv_unsigned ra :: tr
   /\ rng RNG lo (top - lo))
  \/ (top <= bv_unsigned sp + 16 /\ bv_unsigned sp < 2^47 /\ trc = []) ->
  bv_unsigned s0 <> bv_unsigned sp + 8 ->
  0 <= bot -> bot < bv_unsigned sp -> bot + 4096 <= top -> top <= 2^47 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> ACALLOC_PC ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  evtF asegs RNG (calloc_pre_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc nm sz n t lo trc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ACALLOC_SYM) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 5).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 6).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 7).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 8).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 9).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 10).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 11).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 12).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 13).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 14).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 15).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 16).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 17).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 18).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 19).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 20).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 21).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 22).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 23).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 24).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 25).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 26).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 27).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 28).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 29).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 30).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 31).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 32).
Variable F : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 33).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 34).
Variable m : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 35).
Variable nm : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 36).
Variable sz : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 37).
Variable n : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 38).
Variable t : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 39).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 40).
Variable top : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 41).
Variable bot : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 42).
Variable tr : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 43).
Variable trc : ltac2:(SecDietF.SzSecF.ty 'calloc_pre_spec__stmt 44).
#[using="Type"] Lemma calloc_pre_spec__body : ltac:(let T := type of (fun (h : calloc_pre_spec__stmt) => h L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m nm sz n t lo top bot tr trc) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (nm, (sz, (n, (t, (lo, (top, (bot, (tr, trc))))))))))))))))))))))))))))))))))))))))))))) as _.
 cbv zeta.
  intros ST CEIL LO MI TP Ha0 Ha1 NM1 SZ1 EN N PRIM SP16 AC PC LS1 CT8 GPG PGC CX8 TT0 TT SW UW CX0 CX1 CXS T0 T1 TAL TS CT2
         ARM S0NE B0 BB BTOP TOP RA4 RANE RIMG RTLS RSTK RCTX RT. band_lin.   (* [comment removed for export] *)
  assert (LTRC : (length trc <= 29)%nat) by (destruct ARM as [(_ & _ & L1 & -> & _)|(_ & _ & ->)]; cbn [length]; lia).
  assert (SP47 : bv_unsigned sp < 2^47) by (destruct ARM as [(X1 & _)|(_ & X2 & _)]; lia).
  pose proof AC as AC'. (nd_pre AC' 8%nat; intros INI RSS IMAX TI TK T88 TSD CT; nd_post).
  unfold AIMG_HI, AINSTANCE, ATP88, ATSD, ATSDI, ATSDK, AINITED, ARSSLIM, GOT_PGSZ, APGSZ, ACALLOC_PC in *.
  word_range sp SPR. word_range s0 S0R. word_range ra RAR.
  (pose proof (prim_facts n N PRIM) as ndP__; nd_pre ndP__ 8%nat; intros NS RZR RZE RZM RLR RSR RSM NSR; nd_post).
  assert (OV : nm * sz < 2^64) by (rewrite <- EN; clear -NS RZR RZE RZM RLR RSR RSM NSR N; lia).
  box CT2.
  (nd_pre PC 7%nat; intros GOT GOT80 REAL PC4 PC5 PC6 PC7; nd_post).
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (cicptA_spec RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m nm sz lo);
      try eassumption; try (clear -NM1 SZ1 OV LO; nia); try lia; try solve_rng. }
  cbv beta. intros ms1 PA. unfold cicptA_post in PA.
  (nd_pre PA 14%nat; intros t0a t1a t2a a6a a7a t3a t4a t5a t6a m1 junk0 junk1 junk2 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 8%nat; intros MUa WMa MIa STa FRP FRA FRt FRs; nd_post).
  (* [comment removed for export] *)
  pose proof FRs as FRs0. rw_split FRs0 8%nat FRsx FRsr. clear FRsx.
  destruct FRsr as [[_ BSR] _]. cbn [cells_bytes cbytes app] in BSR. rewrite app_nil_r in BSR.
  apply bytes_at_app in BSR. destruct BSR as [BS0 BRA]. rewrite length_le8 in BRA.
  replace (bv_unsigned sp + -16 + Z.of_nat 8) with (bv_unsigned sp - 8) in BRA by lia.
  replace (bv_unsigned sp + -16) with (bv_unsigned sp - 16) in BS0 by lia.
  (* [comment removed for export] *)
  xport TI MUa WMa ltac:(lia). xport TK MUa WMa ltac:(lia). xport T88 MUa WMa ltac:(lia). xport TSD MUa WMa ltac:(lia).
  xport CT MUa WMa ltac:(lia). xport GPG MUa WMa ltac:(lia). xport PGC MUa WMa ltac:(lia). xport TT MUa WMa ltac:(lia).
  xport SW MUa WMa ltac:(lia). xport UW MUa WMa ltac:(lia). xport INI MUa WMa ltac:(lia).
  pose proof FRA as FRA0. rw_split FRA0 1%nat FRp FRz. rw_split FRz 1%nat SZC TAG.
  change 2040%nat with (8 * 255)%nat in FRt. destruct (u64arr_of_CB _ _ 255%nat _ FRt) as [TB LTB].
  pose proof FRs as FRs1. rw_split FRs1 1%nat BPJ REST.
  replace (bv_unsigned sp + -2128) with (bv_unsigned sp - 2136 + 8) in SZC by lia.
  replace (bv_unsigned sp + -2120) with (bv_unsigned sp - 2136 + 16) in TB by lia.
  replace (bv_unsigned sp + -80) with (bv_unsigned sp - 2136 + 2056) in BPJ by lia.
  (* [comment removed for export] *)
  step.                                                          (* [comment removed for export] *)
  name_sp sp (-2144).
  eapply evtF_cut with (P := unwind_impl_post (bv_unsigned sp - 2136) 353976 (bv_unsigned sp) t _ _ gp tp _ _ _ _ _ _ _ s7 s8 s9 s10 s11 F fc lo trc m1).
  { destruct ARM as [(BT & UC & LTR & Etrc & RTOP)|(BT & BT2 & Etrc)]; rewrite Etrc.
    - (* [comment removed for export] *)
      assert (UC1 : uchain m1 top 353976 bot (bv_unsigned sp) 29%nat ([bv_unsigned ra] ++ tr)).
      { replace ([bv_unsigned ra] ++ tr) with ((if bv_unsigned ra =? 353976 then [] else [bv_unsigned ra]) ++ tr)
          by (replace (bv_unsigned ra =? 353976) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
        eapply (uc_step m1 top 353976 bot (bv_unsigned sp) 29%nat (bv_unsigned s0) (bv_unsigned ra) tr); try lia.
        - rewrite Z_to_bv_bv_unsigned. exact BS0.
        - rewrite Z_to_bv_bv_unsigned. exact BRA.
        - replace (bv_unsigned ra =? 353976) with false by (symmetry; apply Z.eqb_neq; lia). cbn [Nat.pred].
          destruct (Z_le_gt_dec (bv_unsigned sp + 16) (bv_unsigned s0)) as [GE|LT].
          + eapply uchain_frame; [exact UC|]. intros a Ha. apply MUa. cbn [outside]. rewrite unsigned_lit by lia. split; [lia| exact I].
          + inversion UC; subst; [apply uc_stop; assumption | exfalso | exfalso]; Z.div_mod_to_equations; lia. }
      clear BS0 BRA UC.
      change (bv_unsigned ra :: tr) with ([bv_unsigned ra] ++ tr).
    eapply (unwind_impl_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (bv_unsigned sp - 2136) 353976 (bv_unsigned sp) (al_ctx L) t top bot lo (words_of_bytes junk1) ([bv_unsigned ra] ++ tr)).
        all: try lazymatch goal with
             | |- stk _ _ _ _ => rewrite Hsp; exact STa
             | |- mem_inv _ _ => exact MIa
             | |- @eq word _ _ => first [reflexivity | exact TP | rewrite Z_to_bv_bv_unsigned; reflexivity | apply Z_to_bv_eqm; rewrite ?unsigned_lit by lia; lia]
             | |- ex _ => first [eexists; exact SZC | eexists; exact BPJ]
             | |- u64arr _ _ _ _ => exact TB
             | |- uchain _ _ _ _ _ _ _ => exact UC1
             | |- _ \/ _ => unboxed CT2
             | |- rng _ _ _ => solve_rng
             | |- rw_cells _ _ (_ + 152) _ => exact CT
             | |- rw_cells _ _ (_ + 8) [C8 _; C8 _] => exact TT
             | |- rw_cells _ _ (_ + 40) _ => exact SW
             | |- rw_cells _ _ (_ + 3168) _ => exact UW
             end.
        all: try eassumption. all: try (unfold AIMG_HI; lia). all: try (Z.div_mod_to_equations; lia).
        all: match goal with |- ?G => idtac "REMU" G end.
    - (* [comment removed for export] *)
      clear BS0 BRA.
    eapply (unwind_impl_spec0 RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (bv_unsigned sp - 2136) 353976 (bv_unsigned sp) (al_ctx L) t top bot lo (words_of_bytes junk1)).
        all: try lazymatch goal with
             | |- stk _ _ _ _ => rewrite Hsp; exact STa
             | |- mem_inv _ _ => exact MIa
             | |- @eq word _ _ => first [reflexivity | exact TP | rewrite Z_to_bv_bv_unsigned; reflexivity | apply Z_to_bv_eqm; rewrite ?unsigned_lit by lia; lia]
             | |- ex _ => first [eexists; exact SZC | eexists; exact BPJ]
             | |- u64arr _ _ _ _ => exact TB
             | |- uchain _ _ _ _ _ _ _ => exact UC1
             | |- _ \/ _ => unboxed CT2
             | |- rng _ _ _ => solve_rng
             | |- rw_cells _ _ (_ + 152) _ => exact CT
             | |- rw_cells _ _ (_ + 8) [C8 _; C8 _] => exact TT
             | |- rw_cells _ _ (_ + 40) _ => exact SW
             | |- rw_cells _ _ (_ + 3168) _ => exact UW
             end.
        all: try eassumption. all: try (unfold AIMG_HI; lia). all: try (Z.div_mod_to_equations; lia).
        all: match goal with |- ?G => idtac "REMU" G end. }

  cbv beta. intros ms2 PU. unfold unwind_impl_post in PU.
  (nd_pre PU 18%nat; intros t0b t1b t2b a0b a1b a2b a3b a4b a5b a6b a7b t3b t4b t5b t6b m2 tb2 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 10%nat; intros MUu WMu MIu STu SZ2 TB2 LTB2 TRF2 BP2 UW2; nd_post).
  unname_sp. rewrite ?unsigned_lit in MUu by lia. rewrite ?unsigned_lit in STu by lia.
  replace (ret_pc (Z_to_bv 64 354068)) with (Z_to_bv 64 354068) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (cicptB_spec RNG) with (nm := nm) (sz := sz); [exact STu | atop_facts; lia | lia | exact MIu | reflexivity | reflexivity | exact NM1 | exact SZ1 | exact OV | exact RIMG | exact RTLS | solve_rng]. }
  cbv beta. intros ms3 PB. unfold cicptB_post in PB. (nd_pre PB 3%nat; intros m3 frc ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 5%nat; intros MUb WMb MIb STb FR16; nd_post). rewrite <- EN in *.
  (* [comment removed for export] *)
  assert (MU3 : munch [(bv_unsigned sp - 2336, bv_unsigned sp); (t + 3168, t + 3169)]%Z m m3).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUb]]. eapply munch_trans; [| eapply munch_weaken; [| exact MUu]].
    eapply munch_weaken; [| exact MUa]. all: unfold sub_fp; cbn [outside]; intros q Hq; lia. }
  assert (WM3 : wmono asegs m m3). { eapply wmono_trans; [| exact WMb]. eapply wmono_trans; [exact WMa | exact WMu]. }
  assert (MU13 : munch [(bv_unsigned sp - 2336, bv_unsigned sp - 2144); (bv_unsigned sp - 2128, bv_unsigned sp - 2124); (bv_unsigned sp - 2120, bv_unsigned sp - 72); (t + 3168, t + 3169)]%Z m1 m3).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUb]]. eapply munch_weaken; [| exact MUu].
    all: unfold sub_fp; cbn [outside]; intros q Hq; lia. }
  assert (WM13 : wmono asegs m1 m3). { eapply wmono_trans; [exact WMu | exact WMb]. }
  xport INI MU13 WM13 ltac:(lia). xport TI MU13 WM13 ltac:(lia). xport TK MU13 WM13 ltac:(lia). xport T88 MU13 WM13 ltac:(lia).
  xport TSD MU13 WM13 ltac:(lia). xport CT MU13 WM13 ltac:(ub CT2; lia). xport FRp MU13 WM13 ltac:(lia). xport TAG MU13 WM13 ltac:(lia). xport FRP MU13 WM13 ltac:(lia).
  xport REST MU13 WM13 ltac:(lia).
  xport RSS MU3 WM3 ltac:(lia). xport IMAX MU3 WM3 ltac:(lia).
  (* [comment removed for export] *)
  xport SZ2 MUb WMb ltac:(lia). replace (bv_unsigned sp - 2136 + 8) with (bv_unsigned sp + -2128) in SZ2 by lia.
  rw_join SZ2 TAG SZT. apply rw_cells_C4C4_to_C8 in SZT. 2: { cbn [length app]; clear -LTRC; lia. }
  rw_join FRp SZT SS.
  xport TB2 MUb WMb ltac:(rewrite LTB2; lia). xport BP2 MUb WMb ltac:(lia). xport UW2 MUb WMb ltac:(lia).
  rewrite Z_to_bv_bv_unsigned in BP2. rw_join BP2 REST FRS.
  replace (bv_unsigned sp - 2136 + 2056) with (bv_unsigned sp + -80) in FRS by lia.
  (* [comment removed for export] *)
  name_sp sp (-2192).
  step.                                                          (* [comment removed for export] *)
  eapply evtF_mono.
  { eapply (allocA_pre_spec0 RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m3 n (bv_unsigned sp + -2136) (al_ctx L) t lo).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => rewrite Hsp; exact STb
         | |- mem_inv _ _ => exact MIb
         | |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => assumption | |- _ /\ _ => split end)
         | |- @eq word _ _ => first [reflexivity | exact TP]
         | |- _ \/ _ => unboxed CT2
         end.
    all: try lazymatch goal with |- rng _ _ _ => solve_rng end.
    all: try eassumption. all: try (unfold AIMG_HI; lia).
    all: match goal with |- ?G => idtac "REMAL" G end. }
  cbv beta. intros ms4 PL. unfold allocA_pre_post0 in PL.
  (nd_pre PL 13%nat; intros t0c t1c t2c a4c a5c a6c a7c t3c t4c t5c t6c m4 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 5%nat; intros MUl WMl MIl STl [fr0 FRa]; nd_post).
  rewrite ?Hsp in MUl. rewrite ?Hsp in STl. rewrite ?Hsp in FRa.
  xport FR16 MUl WMl ltac:(lia). xport FRP MUl WMl ltac:(lia). xport SS MUl WMl ltac:(lia). xport UW2 MUl WMl ltac:(lia). xport FRS MUl WMl ltac:(lia).
  xport TB2 MUl WMl ltac:(rewrite LTB2; lia).
  unfold calloc_pre_post. lazymatch type of Hsp with bv_unsigned ?spx = _ => exists spx end. do 11 eexists. do 4 eexists. exists fr0, frc, junk0, junk2, tb2, m4.
  split; [reflexivity|]. split; [clear -Hsp; lia|].
  split.
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUl]]. eapply munch_weaken; [| exact MU3].
    all: unfold sub_fp; cbn [outside]; intros q Hq; lia. }
  split; [eapply wmono_trans; [exact WM3 | exact WMl]|]. split; [exact MIl|].
  split; [replace (bv_unsigned sp - 2320) with (bv_unsigned sp + -2192 - 128) by lia; exact STl|].
  split; [replace (bv_unsigned sp - 2320) with (bv_unsigned sp + -2192 - 128) by lia; exact FRa|].
  split; [exact FR16|]. split; [exact FRP|].
  replace (bv_unsigned sp + -2120) with (bv_unsigned sp + -2136 + 16) in SS by lia.
  replace (bv_unsigned sp - 2136 + 16) with (bv_unsigned sp + -2136 + 16) in TB2 by lia.
  split; [exact SS|]. split; [exact TB2|]. split; [exact LTB2|]. split; [exact TRF2|]. split; [exact FRS|]. exact UW2.
  Unshelve. all: try exact STb; try exact STa; try exact STu.
Qed.
End Zd1.
#[using="Type"] Lemma calloc_pre_spec : ltac:(let t := eval cbv delta [calloc_pre_spec__stmt] in calloc_pre_spec__stmt in exact t).
Proof. exact calloc_pre_spec__body. Qed.
End CANSEC1.
End TwB.
End F_acalloc_pre.

(* [comment removed for export] *)
Module F_amalloc_pre.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecSlog__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc1b__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aunwind. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_s__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc1b__A3W.F_aalloc1b OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aunwind OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc1b__A3W.F_aunwind2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_amalloc_iseg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc__A3W.F_amalloc_icpt.
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


(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition malloc_pre_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (n t lo : Z) (trc : list Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (spA : word) t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 (s0A s1A s2A s3A s4A s5A s0i : word) (fr0 junk2 : list byte) (tb : list word) m',
    ms' = MS (mkR (Z_to_bv 64 0x33ea8) (Z_to_bv 64 (bv_unsigned spA + -128)) gp tp t0 t1 t2
                  (Z_to_bv 64 1) (Z_to_bv 64 n)
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 (t + 208)) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 8) a4 a5 a6 a7
                  (Z_to_bv 64 8) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n)
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 t) (Z_to_bv 64 1)
                  t3 t4 t5 t6)
             F (Z_to_bv 64 0x38388) fc None m' (seg_rom asegs)
    /\ bv_unsigned spA = bv_unsigned sp - 2144
    /\ munch [(bv_unsigned sp - 2320, bv_unsigned sp); (t + 3168, t + 3169)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp - 2272)
    /\ rw_cells asegs m' (bv_unsigned sp - 2272)
         [CB 8 fr0; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 16); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5A;
          C8 s4A; C8 s3A; C8 s2A; C8 s1A; C8 s0A; C8 (Z_to_bv 64 0x33bd8)]
    /\ rw_cells asegs m' (bv_unsigned sp + -2144) [C8 s0i; C8 (Z_to_bv 64 0x56488)]
    /\ rw_cells asegs m' (bv_unsigned sp + -2128) [C8 (Z_to_bv 64 (bv_unsigned sp + -2128 + 16)); C8 (Z_to_bv 64 (1 + Z.of_nat (length trc)))]
    /\ u64arr asegs m' (bv_unsigned sp + -2128 + 16) tb /\ length tb = 255%nat
    /\ map bv_unsigned (firstn (Datatypes.S (length trc)) tb) = AMALLOC_PC :: trc
    /\ rw_cells asegs m' (bv_unsigned sp + -72) [C8 sp; CB 8 junk2; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' (t + 3168) [C1 (Z_to_bv 8 0)].

Definition malloc_pre_spec__stmt : Prop := forall (L : alayout) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n t lo top bot : Z) (tr trc : list Z),
  let ctx := al_ctx L in
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 n -> 1 <= n -> is_primary n = true ->
  bv_unsigned sp mod 16 = 0 ->
  (* [comment removed for export] *)
  allocA_cells m ctx t -> poison_cells m ->
  rw_cells asegs m 0xaf2fc [C4 (Z_to_bv 64 30)] ->
  rw_cells asegs m 0x14014a [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m GOT_PGSZ [C8 (Z_to_bv 64 APGSZ)] -> rw_cells asegs m APGSZ [C8 (Z_to_bv 64 4096)] ->
  (* [comment removed for export] *)
  rw_cells asegs m (ctx + 8) [C4 (Z_to_bv 64 0)] -> rw_cells asegs m t [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (t + 8) [C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)] ->
  rw_cells asegs m (t + 40) [C1 (Z_to_bv 8 0)] -> rw_cells asegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> sclr ctx 65536 ->
  iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> t mod 4096 = 0 -> sclr t 4096 ->
  (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  (* [comment removed for export] *)
  (bv_unsigned sp + 16 < top /\ uchain m top AMALLOC_PC (bv_unsigned sp) (bv_unsigned s0) 28%nat tr /\ (length tr <= 28)%nat /\ trc = bv_unsigned ra :: tr
   /\ rng RNG lo (top - lo))
  \/ (top <= bv_unsigned sp + 16 /\ bv_unsigned sp < 2^47 /\ trc = []) ->
  bv_unsigned s0 <> bv_unsigned sp + 8 ->
  0 <= bot -> bot < bv_unsigned sp -> bot + 4096 <= top -> top <= 2^47 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AMALLOC_PC ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  evtF asegs RNG (malloc_pre_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n t lo trc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AMALLOC_SYM) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 5).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 6).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 7).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 8).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 9).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 10).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 11).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 12).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 13).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 14).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 15).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 16).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 17).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 18).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 19).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 20).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 21).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 22).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 23).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 24).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 25).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 26).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 27).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 28).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 29).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 30).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 31).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 32).
Variable F : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 33).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 34).
Variable m : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 35).
Variable n : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 36).
Variable t : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 37).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 38).
Variable top : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 39).
Variable bot : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 40).
Variable tr : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 41).
Variable trc : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 42).
#[using="Type"] Lemma malloc_pre_spec__body : ltac:(let T := type of (fun (h : malloc_pre_spec__stmt) => h L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n t lo top bot tr trc) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (n, (t, (lo, (top, (bot, (tr, trc))))))))))))))))))))))))))))))))))))))))))) as _.
 cbv zeta.
  intros ST CEIL LO MI TP Ha0 N PRIM SP16 AC PC LS1 CT8 GPG PGC CX8 TT0 TT SW UW CX0 CX1 CXS T0 T1 TAL TS CT2
         ARM S0NE B0 BB BTOP TOP RA4 RANE RIMG RTLS RSTK RCTX RT. band_lin.   (* [comment removed for export] *)
  assert (LTRC : (length trc <= 29)%nat) by (destruct ARM as [(_ & _ & L1 & -> & _)|(_ & _ & ->)]; cbn [length]; lia).
  assert (SP47 : bv_unsigned sp < 2^47) by (destruct ARM as [(X1 & _)|(_ & X2 & _)]; lia).
  pose proof AC as AC'. (nd_pre AC' 8%nat; intros INI RSS IMAX TI TK T88 TSD CT; nd_post).
  unfold AIMG_HI, AINSTANCE, ATP88, ATSD, ATSDI, ATSDK, AINITED, ARSSLIM, GOT_PGSZ, APGSZ, AMALLOC_SYM, AMALLOC_PC in *.
  word_range sp SPR. word_range s0 S0R. word_range ra RAR.
  (pose proof (prim_facts n N PRIM) as ndP__; nd_pre ndP__ 8%nat; intros NS RZR RZE RZM RLR RSR RSM NSR; nd_post).
  box CT2.
  (nd_pre PC 7%nat; intros GOT GOT80 REAL PC4 PC5 PC6 PC7; nd_post).
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (icptA_spec RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n lo);
      try eassumption; try lia; try solve_rng. }
  cbv beta. intros ms1 PA. unfold icptA_post in PA.
  (nd_pre PA 13%nat; intros t0a t1a t2a a6a a7a t3a t4a t5a t6a m1 junk1 junk2 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 7%nat; intros MUa WMa MIa STa FRA FRt FRs; nd_post).
  (* [comment removed for export] *)
  pose proof FRs as FRs0. rw_split FRs0 7%nat FRsx FRsr. clear FRsx.
  destruct FRsr as [[_ BSR] _]. cbn [cells_bytes cbytes app] in BSR. rewrite app_nil_r in BSR.
  apply bytes_at_app in BSR. destruct BSR as [BS0 BRA]. rewrite length_le8 in BRA.
  replace (bv_unsigned sp + -16 + Z.of_nat 8) with (bv_unsigned sp - 8) in BRA by lia.
  replace (bv_unsigned sp + -16) with (bv_unsigned sp - 16) in BS0 by lia.
  (* [comment removed for export] *)
  xport TI MUa WMa ltac:(lia). xport TK MUa WMa ltac:(lia). xport T88 MUa WMa ltac:(lia). xport TSD MUa WMa ltac:(lia).
  xport CT MUa WMa ltac:(lia). xport GPG MUa WMa ltac:(lia). xport PGC MUa WMa ltac:(lia). xport TT MUa WMa ltac:(lia).
  xport SW MUa WMa ltac:(lia). xport UW MUa WMa ltac:(lia). xport INI MUa WMa ltac:(lia).
  pose proof FRA as FRA0. rw_split FRA0 1%nat FRp FRz. rw_split FRz 1%nat SZC TAG.
  change 2040%nat with (8 * 255)%nat in FRt. destruct (u64arr_of_CB _ _ 255%nat _ FRt) as [TB LTB].
  pose proof FRs as FRs1. rw_split FRs1 1%nat BPJ REST.
  replace (bv_unsigned sp + -2120) with (bv_unsigned sp - 2128 + 8) in SZC by lia.
  replace (bv_unsigned sp + -2112) with (bv_unsigned sp - 2128 + 16) in TB by lia.
  replace (bv_unsigned sp + -72) with (bv_unsigned sp - 2128 + 2056) in BPJ by lia.
  (* [comment removed for export] *)
  step.                                                          (* [comment removed for export] *)
  name_sp sp (-2128).
  eapply evtF_cut with (P := unwind_impl_post (bv_unsigned sp - 2128) 353308 (bv_unsigned sp) t _ _ gp tp _ _ _ _ _ _ s6 s7 s8 s9 s10 s11 F fc lo trc m1).
  { destruct ARM as [(BT & UC & LTR & Etrc & RTOP)|(BT & BT2 & Etrc)]; rewrite Etrc.
    - (* [comment removed for export] *)
      assert (UC1 : uchain m1 top 353308 bot (bv_unsigned sp) 29%nat ([bv_unsigned ra] ++ tr)).
      { replace ([bv_unsigned ra] ++ tr) with ((if bv_unsigned ra =? 353308 then [] else [bv_unsigned ra]) ++ tr)
          by (replace (bv_unsigned ra =? 353308) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
        eapply (uc_step m1 top 353308 bot (bv_unsigned sp) 29%nat (bv_unsigned s0) (bv_unsigned ra) tr); try lia.
        - rewrite Z_to_bv_bv_unsigned. exact BS0.
        - rewrite Z_to_bv_bv_unsigned. exact BRA.
        - replace (bv_unsigned ra =? 353308) with false by (symmetry; apply Z.eqb_neq; lia). cbn [Nat.pred].
          destruct (Z_le_gt_dec (bv_unsigned sp + 16) (bv_unsigned s0)) as [GE|LT].
          + eapply uchain_frame; [exact UC|]. intros a Ha. apply MUa. cbn [outside]. rewrite unsigned_lit by lia. split; [lia| exact I].
          + inversion UC; subst; [apply uc_stop; assumption | exfalso | exfalso]; Z.div_mod_to_equations; lia. }
      clear BS0 BRA UC.
      change (bv_unsigned ra :: tr) with ([bv_unsigned ra] ++ tr).
    eapply (unwind_impl_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (bv_unsigned sp - 2128) 353308 (bv_unsigned sp) (al_ctx L) t top bot lo (words_of_bytes junk1) ([bv_unsigned ra] ++ tr)).
        all: try lazymatch goal with
             | |- stk _ _ _ _ => rewrite Hsp; exact STa
             | |- mem_inv _ _ => exact MIa
             | |- @eq word _ _ => first [reflexivity | exact TP | rewrite Z_to_bv_bv_unsigned; reflexivity | apply Z_to_bv_eqm; rewrite ?unsigned_lit by lia; lia]
             | |- ex _ => first [eexists; exact SZC | eexists; exact BPJ]
             | |- u64arr _ _ _ _ => exact TB
             | |- uchain _ _ _ _ _ _ _ => exact UC1
             | |- _ \/ _ => unboxed CT2
             | |- rng _ _ _ => solve_rng
             | |- rw_cells _ _ (_ + 152) _ => exact CT
             | |- rw_cells _ _ (_ + 8) [C8 _; C8 _] => exact TT
             | |- rw_cells _ _ (_ + 40) _ => exact SW
             | |- rw_cells _ _ (_ + 3168) _ => exact UW
             end.
        all: try eassumption. all: try (unfold AIMG_HI; lia). all: try (Z.div_mod_to_equations; lia).
        all: match goal with |- ?G => idtac "REMU" G end.
    - (* [comment removed for export] *)
      clear BS0 BRA.
    eapply (unwind_impl_spec0 RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (bv_unsigned sp - 2128) 353308 (bv_unsigned sp) (al_ctx L) t top bot lo (words_of_bytes junk1)).
        all: try lazymatch goal with
             | |- stk _ _ _ _ => rewrite Hsp; exact STa
             | |- mem_inv _ _ => exact MIa
             | |- @eq word _ _ => first [reflexivity | exact TP | rewrite Z_to_bv_bv_unsigned; reflexivity | apply Z_to_bv_eqm; rewrite ?unsigned_lit by lia; lia]
             | |- ex _ => first [eexists; exact SZC | eexists; exact BPJ]
             | |- u64arr _ _ _ _ => exact TB
             | |- uchain _ _ _ _ _ _ _ => exact UC1
             | |- _ \/ _ => unboxed CT2
             | |- rng _ _ _ => solve_rng
             | |- rw_cells _ _ (_ + 152) _ => exact CT
             | |- rw_cells _ _ (_ + 8) [C8 _; C8 _] => exact TT
             | |- rw_cells _ _ (_ + 40) _ => exact SW
             | |- rw_cells _ _ (_ + 3168) _ => exact UW
             end.
        all: try eassumption. all: try (unfold AIMG_HI; lia). all: try (Z.div_mod_to_equations; lia).
        all: match goal with |- ?G => idtac "REMU" G end. }

  cbv beta. intros ms2 PU. unfold unwind_impl_post in PU.
  (nd_pre PU 18%nat; intros t0b t1b t2b a0b a1b a2b a3b a4b a5b a6b a7b t3b t4b t5b t6b m2 tb2 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 10%nat; intros MUu WMu MIu STu SZ2 TB2 LTB2 TRF2 BP2 UW2; nd_post).
  unname_sp. rewrite ?unsigned_lit in MUu by lia. rewrite ?unsigned_lit in STu by lia.
  replace (ret_pc (Z_to_bv 64 353400)) with (Z_to_bv 64 353400) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (icptB_spec RNG); [exact STu | atop_facts; lia | lia | exact MIu | reflexivity | exact RIMG | exact RTLS | solve_rng]. }
  cbv beta. intros ms3 PB. unfold icptB_post in PB. (nd_pre PB 2%nat; intros m3 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 5%nat; intros MUb WMb MIb STb FR16; nd_post).
  (* [comment removed for export] *)
  assert (MU3 : munch [(bv_unsigned sp - 2288, bv_unsigned sp); (t + 3168, t + 3169)]%Z m m3).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUb]]. eapply munch_trans; [| eapply munch_weaken; [| exact MUu]].
    eapply munch_weaken; [| exact MUa]. all: unfold sub_fp; cbn [outside]; intros q Hq; lia. }
  assert (WM3 : wmono asegs m m3). { eapply wmono_trans; [| exact WMb]. eapply wmono_trans; [exact WMa | exact WMu]. }
  assert (MU13 : munch [(bv_unsigned sp - 2288, bv_unsigned sp - 2128); (bv_unsigned sp - 2120, bv_unsigned sp - 2116); (bv_unsigned sp - 2112, bv_unsigned sp - 64); (t + 3168, t + 3169)]%Z m1 m3).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUb]]. eapply munch_weaken; [| exact MUu].
    all: unfold sub_fp; cbn [outside]; intros q Hq; lia. }
  assert (WM13 : wmono asegs m1 m3). { eapply wmono_trans; [exact WMu | exact WMb]. }
  xport INI MU13 WM13 ltac:(lia). xport TI MU13 WM13 ltac:(lia). xport TK MU13 WM13 ltac:(lia). xport T88 MU13 WM13 ltac:(lia).
  xport TSD MU13 WM13 ltac:(lia). xport CT MU13 WM13 ltac:(ub CT2; lia). xport FRp MU13 WM13 ltac:(lia). xport TAG MU13 WM13 ltac:(lia).
  xport REST MU13 WM13 ltac:(lia).
  xport RSS MU3 WM3 ltac:(lia). xport IMAX MU3 WM3 ltac:(lia).
  (* [comment removed for export] *)
  xport SZ2 MUb WMb ltac:(lia). replace (bv_unsigned sp - 2128 + 8) with (bv_unsigned sp + -2120) in SZ2 by lia.
  rw_join SZ2 TAG SZT. apply rw_cells_C4C4_to_C8 in SZT. 2: { cbn [length app]; clear -LTRC; lia. }
  rw_join FRp SZT SS.
  xport TB2 MUb WMb ltac:(rewrite LTB2; lia). xport BP2 MUb WMb ltac:(lia). xport UW2 MUb WMb ltac:(lia).
  rewrite Z_to_bv_bv_unsigned in BP2. rw_join BP2 REST FRS.
  replace (bv_unsigned sp - 2128 + 2056) with (bv_unsigned sp + -72) in FRS by lia.
  (* [comment removed for export] *)
  name_sp sp (-2144).
  step.                                                          (* [comment removed for export] *)
  eapply evtF_mono.
  { eapply (allocA_pre_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m3 n (bv_unsigned sp + -2128) (al_ctx L) t lo).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => rewrite Hsp; exact STb
         | |- mem_inv _ _ => exact MIb
         | |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => assumption | |- _ /\ _ => split end)
         | |- @eq word _ _ => first [reflexivity | exact TP]
         | |- _ \/ _ => unboxed CT2
         end.
    all: try lazymatch goal with |- rng _ _ _ => solve_rng end.
    all: try eassumption. all: try (unfold AIMG_HI; lia).
    all: match goal with |- ?G => idtac "REMAL" G end. }
  cbv beta. intros ms4 PL. unfold allocA_pre_post in PL.
  (nd_pre PL 13%nat; intros t0c t1c t2c a4c a5c a6c a7c t3c t4c t5c t6c m4 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 5%nat; intros MUl WMl MIl STl [fr0 FRa]; nd_post).
  rewrite ?Hsp in MUl. rewrite ?Hsp in STl. rewrite ?Hsp in FRa.
  xport FR16 MUl WMl ltac:(lia). xport SS MUl WMl ltac:(lia). xport UW2 MUl WMl ltac:(lia). xport FRS MUl WMl ltac:(lia).
  xport TB2 MUl WMl ltac:(rewrite LTB2; lia).
  unfold malloc_pre_post. lazymatch type of Hsp with bv_unsigned ?spx = _ => exists spx end. do 11 eexists. do 7 eexists. exists fr0, junk2, tb2, m4.
  split; [reflexivity|]. split; [clear -Hsp; lia|].
  split.
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUl]]. eapply munch_weaken; [| exact MU3].
    all: unfold sub_fp; cbn [outside]; intros q Hq; lia. }
  split; [eapply wmono_trans; [exact WM3 | exact WMl]|]. split; [exact MIl|].
  split; [replace (bv_unsigned sp - 2272) with (bv_unsigned sp + -2144 - 128) by lia; exact STl|].
  split; [replace (bv_unsigned sp - 2272) with (bv_unsigned sp + -2144 - 128) by lia; exact FRa|].
  split; [exact FR16|].
  replace (bv_unsigned sp + -2112) with (bv_unsigned sp + -2128 + 16) in SS by lia.
  replace (bv_unsigned sp - 2128 + 16) with (bv_unsigned sp + -2128 + 16) in TB2 by lia.
  split; [exact SS|]. split; [exact TB2|]. split; [exact LTB2|]. split; [exact TRF2|]. split; [exact FRS|]. exact UW2.
  Unshelve. all: try exact STb; try exact STa; try exact STu.
Qed.
End Zd1.
#[using="Type"] Lemma malloc_pre_spec : ltac:(let t := eval cbv delta [malloc_pre_spec__stmt] in malloc_pre_spec__stmt in exact t).
Proof. exact malloc_pre_spec__body. Qed.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc1b__A3W.F_aalloc1b.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aunwind.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc1b__A3W.F_aunwind2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_amalloc_iseg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc__A3W.F_amalloc_icpt.TwB.
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


(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition malloc_pre_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (n t lo : Z) (trc : list Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (spA : word) t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 (s0A s1A s2A s3A s4A s5A s0i : word) (fr0 junk2 : list byte) (tb : list word) m',
    ms' = MS (mkR (Z_to_bv 64 0x33f10) (Z_to_bv 64 (bv_unsigned spA + -128)) gp tp t0 t1 t2
                  (Z_to_bv 64 1) (Z_to_bv 64 n)
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 (t + 208)) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 8) a4 a5 a6 a7
                  (Z_to_bv 64 8) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n)
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 t) (Z_to_bv 64 1)
                  t3 t4 t5 t6)
             F (Z_to_bv 64 0x383f0) fc None m' (seg_rom asegs)
    /\ bv_unsigned spA = bv_unsigned sp - 2144
    /\ munch [(bv_unsigned sp - 2320, bv_unsigned sp); (t + 3168, t + 3169)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp - 2272)
    /\ rw_cells asegs m' (bv_unsigned sp - 2272)
         [CB 8 fr0; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 16); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5A;
          C8 s4A; C8 s3A; C8 s2A; C8 s1A; C8 s0A; C8 (Z_to_bv 64 0x33c40)]
    /\ rw_cells asegs m' (bv_unsigned sp + -2144) [C8 s0i; C8 (Z_to_bv 64 0x564f0)]
    /\ rw_cells asegs m' (bv_unsigned sp + -2128) [C8 (Z_to_bv 64 (bv_unsigned sp + -2128 + 16)); C8 (Z_to_bv 64 (1 + Z.of_nat (length trc)))]
    /\ u64arr asegs m' (bv_unsigned sp + -2128 + 16) tb /\ length tb = 255%nat
    /\ map bv_unsigned (firstn (Datatypes.S (length trc)) tb) = AMALLOC_PC :: trc
    /\ rw_cells asegs m' (bv_unsigned sp + -72) [C8 sp; CB 8 junk2; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' (t + 3168) [C1 (Z_to_bv 8 0)].

Definition malloc_pre_spec__stmt : Prop := forall (L : alayout) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n t lo top bot : Z) (tr trc : list Z),
  let ctx := al_ctx L in
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 n -> 1 <= n -> is_primary n = true ->
  bv_unsigned sp mod 16 = 0 ->
  (* [comment removed for export] *)
  allocA_cells m ctx t -> poison_cells m ->
  rw_cells asegs m 0xaf6fc [C4 (Z_to_bv 64 30)] ->
  rw_cells asegs m 0x14054a [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m GOT_PGSZ [C8 (Z_to_bv 64 APGSZ)] -> rw_cells asegs m APGSZ [C8 (Z_to_bv 64 4096)] ->
  (* [comment removed for export] *)
  rw_cells asegs m (ctx + 8) [C4 (Z_to_bv 64 0)] -> rw_cells asegs m t [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (t + 8) [C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)] ->
  rw_cells asegs m (t + 40) [C1 (Z_to_bv 8 0)] -> rw_cells asegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> sclr ctx 65536 ->
  iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> t mod 4096 = 0 -> sclr t 4096 ->
  (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  (* [comment removed for export] *)
  (bv_unsigned sp + 16 < top /\ uchain m top AMALLOC_PC (bv_unsigned sp) (bv_unsigned s0) 28%nat tr /\ (length tr <= 28)%nat /\ trc = bv_unsigned ra :: tr
   /\ rng RNG lo (top - lo))
  \/ (top <= bv_unsigned sp + 16 /\ bv_unsigned sp < 2^47 /\ trc = []) ->
  bv_unsigned s0 <> bv_unsigned sp + 8 ->
  0 <= bot -> bot < bv_unsigned sp -> bot + 4096 <= top -> top <= 2^47 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AMALLOC_PC ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  evtF asegs RNG (malloc_pre_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n t lo trc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AMALLOC_SYM) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 5).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 6).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 7).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 8).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 9).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 10).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 11).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 12).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 13).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 14).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 15).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 16).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 17).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 18).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 19).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 20).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 21).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 22).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 23).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 24).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 25).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 26).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 27).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 28).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 29).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 30).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 31).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 32).
Variable F : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 33).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 34).
Variable m : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 35).
Variable n : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 36).
Variable t : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 37).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 38).
Variable top : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 39).
Variable bot : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 40).
Variable tr : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 41).
Variable trc : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec__stmt 42).
#[using="Type"] Lemma malloc_pre_spec__body : ltac:(let T := type of (fun (h : malloc_pre_spec__stmt) => h L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n t lo top bot tr trc) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (n, (t, (lo, (top, (bot, (tr, trc))))))))))))))))))))))))))))))))))))))))))) as _.
 cbv zeta.
  intros ST CEIL LO MI TP Ha0 N PRIM SP16 AC PC LS1 CT8 GPG PGC CX8 TT0 TT SW UW CX0 CX1 CXS T0 T1 TAL TS CT2
         ARM S0NE B0 BB BTOP TOP RA4 RANE RIMG RTLS RSTK RCTX RT. band_lin.   (* [comment removed for export] *)
  assert (LTRC : (length trc <= 29)%nat) by (destruct ARM as [(_ & _ & L1 & -> & _)|(_ & _ & ->)]; cbn [length]; lia).
  assert (SP47 : bv_unsigned sp < 2^47) by (destruct ARM as [(X1 & _)|(_ & X2 & _)]; lia).
  pose proof AC as AC'. (nd_pre AC' 8%nat; intros INI RSS IMAX TI TK T88 TSD CT; nd_post).
  unfold AIMG_HI, AINSTANCE, ATP88, ATSD, ATSDI, ATSDK, AINITED, ARSSLIM, GOT_PGSZ, APGSZ, AMALLOC_SYM, AMALLOC_PC in *.
  word_range sp SPR. word_range s0 S0R. word_range ra RAR.
  (pose proof (prim_facts n N PRIM) as ndP__; nd_pre ndP__ 8%nat; intros NS RZR RZE RZM RLR RSR RSM NSR; nd_post).
  box CT2.
  (nd_pre PC 7%nat; intros GOT GOT80 REAL PC4 PC5 PC6 PC7; nd_post).
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (icptA_spec RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n lo);
      try eassumption; try lia; try solve_rng. }
  cbv beta. intros ms1 PA. unfold icptA_post in PA.
  (nd_pre PA 13%nat; intros t0a t1a t2a a6a a7a t3a t4a t5a t6a m1 junk1 junk2 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 7%nat; intros MUa WMa MIa STa FRA FRt FRs; nd_post).
  (* [comment removed for export] *)
  pose proof FRs as FRs0. rw_split FRs0 7%nat FRsx FRsr. clear FRsx.
  destruct FRsr as [[_ BSR] _]. cbn [cells_bytes cbytes app] in BSR. rewrite app_nil_r in BSR.
  apply bytes_at_app in BSR. destruct BSR as [BS0 BRA]. rewrite length_le8 in BRA.
  replace (bv_unsigned sp + -16 + Z.of_nat 8) with (bv_unsigned sp - 8) in BRA by lia.
  replace (bv_unsigned sp + -16) with (bv_unsigned sp - 16) in BS0 by lia.
  (* [comment removed for export] *)
  xport TI MUa WMa ltac:(lia). xport TK MUa WMa ltac:(lia). xport T88 MUa WMa ltac:(lia). xport TSD MUa WMa ltac:(lia).
  xport CT MUa WMa ltac:(lia). xport GPG MUa WMa ltac:(lia). xport PGC MUa WMa ltac:(lia). xport TT MUa WMa ltac:(lia).
  xport SW MUa WMa ltac:(lia). xport UW MUa WMa ltac:(lia). xport INI MUa WMa ltac:(lia).
  pose proof FRA as FRA0. rw_split FRA0 1%nat FRp FRz. rw_split FRz 1%nat SZC TAG.
  change 2040%nat with (8 * 255)%nat in FRt. destruct (u64arr_of_CB _ _ 255%nat _ FRt) as [TB LTB].
  pose proof FRs as FRs1. rw_split FRs1 1%nat BPJ REST.
  replace (bv_unsigned sp + -2120) with (bv_unsigned sp - 2128 + 8) in SZC by lia.
  replace (bv_unsigned sp + -2112) with (bv_unsigned sp - 2128 + 16) in TB by lia.
  replace (bv_unsigned sp + -72) with (bv_unsigned sp - 2128 + 2056) in BPJ by lia.
  (* [comment removed for export] *)
  step.                                                          (* [comment removed for export] *)
  name_sp sp (-2128).
  eapply evtF_cut with (P := unwind_impl_post (bv_unsigned sp - 2128) 353412 (bv_unsigned sp) t _ _ gp tp _ _ _ _ _ _ s6 s7 s8 s9 s10 s11 F fc lo trc m1).
  { destruct ARM as [(BT & UC & LTR & Etrc & RTOP)|(BT & BT2 & Etrc)]; rewrite Etrc.
    - (* [comment removed for export] *)
      assert (UC1 : uchain m1 top 353412 bot (bv_unsigned sp) 29%nat ([bv_unsigned ra] ++ tr)).
      { replace ([bv_unsigned ra] ++ tr) with ((if bv_unsigned ra =? 353412 then [] else [bv_unsigned ra]) ++ tr)
          by (replace (bv_unsigned ra =? 353412) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
        eapply (uc_step m1 top 353412 bot (bv_unsigned sp) 29%nat (bv_unsigned s0) (bv_unsigned ra) tr); try lia.
        - rewrite Z_to_bv_bv_unsigned. exact BS0.
        - rewrite Z_to_bv_bv_unsigned. exact BRA.
        - replace (bv_unsigned ra =? 353412) with false by (symmetry; apply Z.eqb_neq; lia). cbn [Nat.pred].
          destruct (Z_le_gt_dec (bv_unsigned sp + 16) (bv_unsigned s0)) as [GE|LT].
          + eapply uchain_frame; [exact UC|]. intros a Ha. apply MUa. cbn [outside]. rewrite unsigned_lit by lia. split; [lia| exact I].
          + inversion UC; subst; [apply uc_stop; assumption | exfalso | exfalso]; Z.div_mod_to_equations; lia. }
      clear BS0 BRA UC.
      change (bv_unsigned ra :: tr) with ([bv_unsigned ra] ++ tr).
    eapply (unwind_impl_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (bv_unsigned sp - 2128) 353412 (bv_unsigned sp) (al_ctx L) t top bot lo (words_of_bytes junk1) ([bv_unsigned ra] ++ tr)).
        all: try lazymatch goal with
             | |- stk _ _ _ _ => rewrite Hsp; exact STa
             | |- mem_inv _ _ => exact MIa
             | |- @eq word _ _ => first [reflexivity | exact TP | rewrite Z_to_bv_bv_unsigned; reflexivity | apply Z_to_bv_eqm; rewrite ?unsigned_lit by lia; lia]
             | |- ex _ => first [eexists; exact SZC | eexists; exact BPJ]
             | |- u64arr _ _ _ _ => exact TB
             | |- uchain _ _ _ _ _ _ _ => exact UC1
             | |- _ \/ _ => unboxed CT2
             | |- rng _ _ _ => solve_rng
             | |- rw_cells _ _ (_ + 152) _ => exact CT
             | |- rw_cells _ _ (_ + 8) [C8 _; C8 _] => exact TT
             | |- rw_cells _ _ (_ + 40) _ => exact SW
             | |- rw_cells _ _ (_ + 3168) _ => exact UW
             end.
        all: try eassumption. all: try (unfold AIMG_HI; lia). all: try (Z.div_mod_to_equations; lia).
        all: match goal with |- ?G => idtac "REMU" G end.
    - (* [comment removed for export] *)
      clear BS0 BRA.
    eapply (unwind_impl_spec0 RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (bv_unsigned sp - 2128) 353412 (bv_unsigned sp) (al_ctx L) t top bot lo (words_of_bytes junk1)).
        all: try lazymatch goal with
             | |- stk _ _ _ _ => rewrite Hsp; exact STa
             | |- mem_inv _ _ => exact MIa
             | |- @eq word _ _ => first [reflexivity | exact TP | rewrite Z_to_bv_bv_unsigned; reflexivity | apply Z_to_bv_eqm; rewrite ?unsigned_lit by lia; lia]
             | |- ex _ => first [eexists; exact SZC | eexists; exact BPJ]
             | |- u64arr _ _ _ _ => exact TB
             | |- uchain _ _ _ _ _ _ _ => exact UC1
             | |- _ \/ _ => unboxed CT2
             | |- rng _ _ _ => solve_rng
             | |- rw_cells _ _ (_ + 152) _ => exact CT
             | |- rw_cells _ _ (_ + 8) [C8 _; C8 _] => exact TT
             | |- rw_cells _ _ (_ + 40) _ => exact SW
             | |- rw_cells _ _ (_ + 3168) _ => exact UW
             end.
        all: try eassumption. all: try (unfold AIMG_HI; lia). all: try (Z.div_mod_to_equations; lia).
        all: match goal with |- ?G => idtac "REMU" G end. }

  cbv beta. intros ms2 PU. unfold unwind_impl_post in PU.
  (nd_pre PU 18%nat; intros t0b t1b t2b a0b a1b a2b a3b a4b a5b a6b a7b t3b t4b t5b t6b m2 tb2 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 10%nat; intros MUu WMu MIu STu SZ2 TB2 LTB2 TRF2 BP2 UW2; nd_post).
  unname_sp. rewrite ?unsigned_lit in MUu by lia. rewrite ?unsigned_lit in STu by lia.
  replace (ret_pc (Z_to_bv 64 353504)) with (Z_to_bv 64 353504) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (icptB_spec RNG); [exact STu | atop_facts; lia | lia | exact MIu | reflexivity | exact RIMG | exact RTLS | solve_rng]. }
  cbv beta. intros ms3 PB. unfold icptB_post in PB. (nd_pre PB 2%nat; intros m3 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 5%nat; intros MUb WMb MIb STb FR16; nd_post).
  (* [comment removed for export] *)
  assert (MU3 : munch [(bv_unsigned sp - 2288, bv_unsigned sp); (t + 3168, t + 3169)]%Z m m3).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUb]]. eapply munch_trans; [| eapply munch_weaken; [| exact MUu]].
    eapply munch_weaken; [| exact MUa]. all: unfold sub_fp; cbn [outside]; intros q Hq; lia. }
  assert (WM3 : wmono asegs m m3). { eapply wmono_trans; [| exact WMb]. eapply wmono_trans; [exact WMa | exact WMu]. }
  assert (MU13 : munch [(bv_unsigned sp - 2288, bv_unsigned sp - 2128); (bv_unsigned sp - 2120, bv_unsigned sp - 2116); (bv_unsigned sp - 2112, bv_unsigned sp - 64); (t + 3168, t + 3169)]%Z m1 m3).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUb]]. eapply munch_weaken; [| exact MUu].
    all: unfold sub_fp; cbn [outside]; intros q Hq; lia. }
  assert (WM13 : wmono asegs m1 m3). { eapply wmono_trans; [exact WMu | exact WMb]. }
  xport INI MU13 WM13 ltac:(lia). xport TI MU13 WM13 ltac:(lia). xport TK MU13 WM13 ltac:(lia). xport T88 MU13 WM13 ltac:(lia).
  xport TSD MU13 WM13 ltac:(lia). xport CT MU13 WM13 ltac:(ub CT2; lia). xport FRp MU13 WM13 ltac:(lia). xport TAG MU13 WM13 ltac:(lia).
  xport REST MU13 WM13 ltac:(lia).
  xport RSS MU3 WM3 ltac:(lia). xport IMAX MU3 WM3 ltac:(lia).
  (* [comment removed for export] *)
  xport SZ2 MUb WMb ltac:(lia). replace (bv_unsigned sp - 2128 + 8) with (bv_unsigned sp + -2120) in SZ2 by lia.
  rw_join SZ2 TAG SZT. apply rw_cells_C4C4_to_C8 in SZT. 2: { cbn [length app]; clear -LTRC; lia. }
  rw_join FRp SZT SS.
  xport TB2 MUb WMb ltac:(rewrite LTB2; lia). xport BP2 MUb WMb ltac:(lia). xport UW2 MUb WMb ltac:(lia).
  rewrite Z_to_bv_bv_unsigned in BP2. rw_join BP2 REST FRS.
  replace (bv_unsigned sp - 2128 + 2056) with (bv_unsigned sp + -72) in FRS by lia.
  (* [comment removed for export] *)
  name_sp sp (-2144).
  step.                                                          (* [comment removed for export] *)
  eapply evtF_mono.
  { eapply (allocA_pre_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m3 n (bv_unsigned sp + -2128) (al_ctx L) t lo).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => rewrite Hsp; exact STb
         | |- mem_inv _ _ => exact MIb
         | |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => assumption | |- _ /\ _ => split end)
         | |- @eq word _ _ => first [reflexivity | exact TP]
         | |- _ \/ _ => unboxed CT2
         end.
    all: try lazymatch goal with |- rng _ _ _ => solve_rng end.
    all: try eassumption. all: try (unfold AIMG_HI; lia).
    all: match goal with |- ?G => idtac "REMAL" G end. }
  cbv beta. intros ms4 PL. unfold allocA_pre_post in PL.
  (nd_pre PL 13%nat; intros t0c t1c t2c a4c a5c a6c a7c t3c t4c t5c t6c m4 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 5%nat; intros MUl WMl MIl STl [fr0 FRa]; nd_post).
  rewrite ?Hsp in MUl. rewrite ?Hsp in STl. rewrite ?Hsp in FRa.
  xport FR16 MUl WMl ltac:(lia). xport SS MUl WMl ltac:(lia). xport UW2 MUl WMl ltac:(lia). xport FRS MUl WMl ltac:(lia).
  xport TB2 MUl WMl ltac:(rewrite LTB2; lia).
  unfold malloc_pre_post. lazymatch type of Hsp with bv_unsigned ?spx = _ => exists spx end. do 11 eexists. do 7 eexists. exists fr0, junk2, tb2, m4.
  split; [reflexivity|]. split; [clear -Hsp; lia|].
  split.
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUl]]. eapply munch_weaken; [| exact MU3].
    all: unfold sub_fp; cbn [outside]; intros q Hq; lia. }
  split; [eapply wmono_trans; [exact WM3 | exact WMl]|]. split; [exact MIl|].
  split; [replace (bv_unsigned sp - 2272) with (bv_unsigned sp + -2144 - 128) by lia; exact STl|].
  split; [replace (bv_unsigned sp - 2272) with (bv_unsigned sp + -2144 - 128) by lia; exact FRa|].
  split; [exact FR16|].
  replace (bv_unsigned sp + -2112) with (bv_unsigned sp + -2128 + 16) in SS by lia.
  replace (bv_unsigned sp - 2128 + 16) with (bv_unsigned sp + -2128 + 16) in TB2 by lia.
  split; [exact SS|]. split; [exact TB2|]. split; [exact LTB2|]. split; [exact TRF2|]. split; [exact FRS|]. exact UW2.
  Unshelve. all: try exact STb; try exact STa; try exact STu.
Qed.
End Zd1.
#[using="Type"] Lemma malloc_pre_spec : ltac:(let t := eval cbv delta [malloc_pre_spec__stmt] in malloc_pre_spec__stmt in exact t).
Proof. exact malloc_pre_spec__body. Qed.
End CANSEC1.
End TwB.
End F_amalloc_pre.

(* [comment removed for export] *)
Module F_amalloc_preS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecFacts. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecSlog__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc1b__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aunwind. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_s__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc1b__A3W.F_aalloc1b OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc1b__A3W.F_aalloc1s OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aunwind OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc1b__A3W.F_aunwind2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_amalloc_iseg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc__A3W.F_amalloc_icpt.
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


(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition malloc_pre_postS (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (n t lo : Z) (trc : list Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (spA : word) t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 (s0A s1A s2A s3A s4A s5A s0i : word) (fr0 junk2 : list byte) (tb : list word) m',
    ms' = MS (mkR (Z_to_bv 64 0x33ea8) (Z_to_bv 64 (bv_unsigned spA + -128)) gp tp t0 t1 t2
                  (Z_to_bv 64 0) (Z_to_bv 64 n)
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 (t + 208)) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 8) a4 a5 a6 a7
                  (Z_to_bv 64 8) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n)
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 t) (Z_to_bv 64 1)
                  t3 t4 t5 t6)
             F (Z_to_bv 64 0x38388) fc None m' (seg_rom asegs)
    /\ bv_unsigned spA = bv_unsigned sp - 2144
    /\ munch [(bv_unsigned sp - 2320, bv_unsigned sp); (t + 3168, t + 3169)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp - 2272)
    /\ rw_cells asegs m' (bv_unsigned sp - 2272)
         [CB 8 fr0; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 16); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5A;
          C8 s4A; C8 s3A; C8 s2A; C8 s1A; C8 s0A; C8 (Z_to_bv 64 0x33bd8)]
    /\ rw_cells asegs m' (bv_unsigned sp + -2144) [C8 s0i; C8 (Z_to_bv 64 0x56488)]
    /\ rw_cells asegs m' (bv_unsigned sp + -2128) [C8 (Z_to_bv 64 (bv_unsigned sp + -2128 + 16)); C8 (Z_to_bv 64 (1 + Z.of_nat (length trc)))]
    /\ u64arr asegs m' (bv_unsigned sp + -2128 + 16) tb /\ length tb = 255%nat
    /\ map bv_unsigned (firstn (Datatypes.S (length trc)) tb) = AMALLOC_PC :: trc
    /\ rw_cells asegs m' (bv_unsigned sp + -72) [C8 sp; CB 8 junk2; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' (t + 3168) [C1 (Z_to_bv 8 0)].

Definition malloc_pre_spec_sec__stmt : Prop := forall (L : alayout) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n t lo top bot : Z) (tr trc : list Z),
  let ctx := al_ctx L in
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 n -> 1 <= n <= AREQMAX -> is_primary n = false ->
  bv_unsigned sp mod 16 = 0 ->
  (* [comment removed for export] *)
  allocA_cells m ctx t -> poison_cells m ->
  rw_cells asegs m 0xaf2fc [C4 (Z_to_bv 64 30)] ->
  rw_cells asegs m 0x14014a [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m GOT_PGSZ [C8 (Z_to_bv 64 APGSZ)] -> rw_cells asegs m APGSZ [C8 (Z_to_bv 64 4096)] ->
  (* [comment removed for export] *)
  rw_cells asegs m (ctx + 8) [C4 (Z_to_bv 64 0)] -> rw_cells asegs m t [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (t + 8) [C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)] ->
  rw_cells asegs m (t + 40) [C1 (Z_to_bv 8 0)] -> rw_cells asegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> sclr ctx 65536 ->
  iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> t mod 4096 = 0 -> sclr t 4096 ->
  (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  (* [comment removed for export] *)
  (bv_unsigned sp + 16 < top /\ uchain m top AMALLOC_PC (bv_unsigned sp) (bv_unsigned s0) 28%nat tr /\ (length tr <= 28)%nat /\ trc = bv_unsigned ra :: tr
   /\ rng RNG lo (top - lo))
  \/ (top <= bv_unsigned sp + 16 /\ bv_unsigned sp < 2^47 /\ trc = []) ->
  bv_unsigned s0 <> bv_unsigned sp + 8 ->
  0 <= bot -> bot < bv_unsigned sp -> bot + 4096 <= top -> top <= 2^47 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AMALLOC_PC ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  evtF asegs RNG (malloc_pre_postS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n t lo trc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AMALLOC_SYM) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 5).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 6).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 7).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 8).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 9).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 10).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 11).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 12).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 13).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 14).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 15).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 16).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 17).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 18).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 19).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 20).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 21).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 22).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 23).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 24).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 25).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 26).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 27).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 28).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 29).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 30).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 31).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 32).
Variable F : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 33).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 34).
Variable m : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 35).
Variable n : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 36).
Variable t : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 37).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 38).
Variable top : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 39).
Variable bot : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 40).
Variable tr : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 41).
Variable trc : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 42).
#[using="Type"] Lemma malloc_pre_spec_sec__body : ltac:(let T := type of (fun (h : malloc_pre_spec_sec__stmt) => h L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n t lo top bot tr trc) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (n, (t, (lo, (top, (bot, (tr, trc))))))))))))))))))))))))))))))))))))))))))) as _.
 cbv zeta.
  intros ST CEIL LO MI TP Ha0 N PRIM SP16 AC PC LS1 CT8 GPG PGC CX8 TT0 TT SW UW CX0 CX1 CXS T0 T1 TAL TS CT2
         ARM S0NE B0 BB BTOP TOP RA4 RANE RIMG RTLS RSTK RCTX RT. band_lin.   (* [comment removed for export] *)
  assert (LTRC : (length trc <= 29)%nat) by (destruct ARM as [(_ & _ & L1 & -> & _)|(_ & _ & ->)]; cbn [length]; lia).
  assert (SP47 : bv_unsigned sp < 2^47) by (destruct ARM as [(X1 & _)|(_ & X2 & _)]; lia).
  pose proof AC as AC'. (nd_pre AC' 8%nat; intros INI RSS IMAX TI TK T88 TSD CT; nd_post).
  unfold AIMG_HI, AINSTANCE, ATP88, ATSD, ATSDI, ATSDK, AINITED, ARSSLIM, GOT_PGSZ, APGSZ, AMALLOC_SYM, AMALLOC_PC in *.
  word_range sp SPR. word_range s0 S0R. word_range ra RAR.
  (pose proof (sec_facts n N PRIM) as ndP__; nd_pre ndP__ 10%nat; intros NB RZ RSE RSR RSM NSE MSE MSR MSM MSB; nd_post).
  box CT2.
  (nd_pre PC 7%nat; intros GOT GOT80 REAL PC4 PC5 PC6 PC7; nd_post).
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (icptA_spec RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n lo);
      try eassumption; try lia; try solve_rng. }
  cbv beta. intros ms1 PA. unfold icptA_post in PA.
  (nd_pre PA 13%nat; intros t0a t1a t2a a6a a7a t3a t4a t5a t6a m1 junk1 junk2 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 7%nat; intros MUa WMa MIa STa FRA FRt FRs; nd_post).
  (* [comment removed for export] *)
  pose proof FRs as FRs0. rw_split FRs0 7%nat FRsx FRsr. clear FRsx.
  destruct FRsr as [[_ BSR] _]. cbn [cells_bytes cbytes app] in BSR. rewrite app_nil_r in BSR.
  apply bytes_at_app in BSR. destruct BSR as [BS0 BRA]. rewrite length_le8 in BRA.
  replace (bv_unsigned sp + -16 + Z.of_nat 8) with (bv_unsigned sp - 8) in BRA by lia.
  replace (bv_unsigned sp + -16) with (bv_unsigned sp - 16) in BS0 by lia.
  (* [comment removed for export] *)
  xport TI MUa WMa ltac:(lia). xport TK MUa WMa ltac:(lia). xport T88 MUa WMa ltac:(lia). xport TSD MUa WMa ltac:(lia).
  xport CT MUa WMa ltac:(lia). xport GPG MUa WMa ltac:(lia). xport PGC MUa WMa ltac:(lia). xport TT MUa WMa ltac:(lia).
  xport SW MUa WMa ltac:(lia). xport UW MUa WMa ltac:(lia). xport INI MUa WMa ltac:(lia).
  pose proof FRA as FRA0. rw_split FRA0 1%nat FRp FRz. rw_split FRz 1%nat SZC TAG.
  change 2040%nat with (8 * 255)%nat in FRt. destruct (u64arr_of_CB _ _ 255%nat _ FRt) as [TB LTB].
  pose proof FRs as FRs1. rw_split FRs1 1%nat BPJ REST.
  replace (bv_unsigned sp + -2120) with (bv_unsigned sp - 2128 + 8) in SZC by lia.
  replace (bv_unsigned sp + -2112) with (bv_unsigned sp - 2128 + 16) in TB by lia.
  replace (bv_unsigned sp + -72) with (bv_unsigned sp - 2128 + 2056) in BPJ by lia.
  (* [comment removed for export] *)
  step.                                                          (* [comment removed for export] *)
  name_sp sp (-2128).
  eapply evtF_cut with (P := unwind_impl_post (bv_unsigned sp - 2128) 353308 (bv_unsigned sp) t _ _ gp tp _ _ _ _ _ _ s6 s7 s8 s9 s10 s11 F fc lo trc m1).
  { destruct ARM as [(BT & UC & LTR & Etrc & RTOP)|(BT & BT2 & Etrc)]; rewrite Etrc.
    - (* [comment removed for export] *)
      assert (UC1 : uchain m1 top 353308 bot (bv_unsigned sp) 29%nat ([bv_unsigned ra] ++ tr)).
      { replace ([bv_unsigned ra] ++ tr) with ((if bv_unsigned ra =? 353308 then [] else [bv_unsigned ra]) ++ tr)
          by (replace (bv_unsigned ra =? 353308) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
        eapply (uc_step m1 top 353308 bot (bv_unsigned sp) 29%nat (bv_unsigned s0) (bv_unsigned ra) tr); try lia.
        - rewrite Z_to_bv_bv_unsigned. exact BS0.
        - rewrite Z_to_bv_bv_unsigned. exact BRA.
        - replace (bv_unsigned ra =? 353308) with false by (symmetry; apply Z.eqb_neq; lia). cbn [Nat.pred].
          destruct (Z_le_gt_dec (bv_unsigned sp + 16) (bv_unsigned s0)) as [GE|LT].
          + eapply uchain_frame; [exact UC|]. intros a Ha. apply MUa. cbn [outside]. rewrite unsigned_lit by lia. split; [lia| exact I].
          + inversion UC; subst; [apply uc_stop; assumption | exfalso | exfalso]; Z.div_mod_to_equations; lia. }
      clear BS0 BRA UC.
      change (bv_unsigned ra :: tr) with ([bv_unsigned ra] ++ tr).
    eapply (unwind_impl_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (bv_unsigned sp - 2128) 353308 (bv_unsigned sp) (al_ctx L) t top bot lo (words_of_bytes junk1) ([bv_unsigned ra] ++ tr)).
        all: try lazymatch goal with
             | |- stk _ _ _ _ => rewrite Hsp; exact STa
             | |- mem_inv _ _ => exact MIa
             | |- @eq word _ _ => first [reflexivity | exact TP | rewrite Z_to_bv_bv_unsigned; reflexivity | apply Z_to_bv_eqm; rewrite ?unsigned_lit by lia; lia]
             | |- ex _ => first [eexists; exact SZC | eexists; exact BPJ]
             | |- u64arr _ _ _ _ => exact TB
             | |- uchain _ _ _ _ _ _ _ => exact UC1
             | |- _ \/ _ => unboxed CT2
             | |- rng _ _ _ => solve_rng
             | |- rw_cells _ _ (_ + 152) _ => exact CT
             | |- rw_cells _ _ (_ + 8) [C8 _; C8 _] => exact TT
             | |- rw_cells _ _ (_ + 40) _ => exact SW
             | |- rw_cells _ _ (_ + 3168) _ => exact UW
             end.
        all: try eassumption. all: try (unfold AIMG_HI; lia). all: try (Z.div_mod_to_equations; lia).
        all: match goal with |- ?G => idtac "REMU" G end.
    - (* [comment removed for export] *)
      clear BS0 BRA.
    eapply (unwind_impl_spec0 RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (bv_unsigned sp - 2128) 353308 (bv_unsigned sp) (al_ctx L) t top bot lo (words_of_bytes junk1)).
        all: try lazymatch goal with
             | |- stk _ _ _ _ => rewrite Hsp; exact STa
             | |- mem_inv _ _ => exact MIa
             | |- @eq word _ _ => first [reflexivity | exact TP | rewrite Z_to_bv_bv_unsigned; reflexivity | apply Z_to_bv_eqm; rewrite ?unsigned_lit by lia; lia]
             | |- ex _ => first [eexists; exact SZC | eexists; exact BPJ]
             | |- u64arr _ _ _ _ => exact TB
             | |- uchain _ _ _ _ _ _ _ => exact UC1
             | |- _ \/ _ => unboxed CT2
             | |- rng _ _ _ => solve_rng
             | |- rw_cells _ _ (_ + 152) _ => exact CT
             | |- rw_cells _ _ (_ + 8) [C8 _; C8 _] => exact TT
             | |- rw_cells _ _ (_ + 40) _ => exact SW
             | |- rw_cells _ _ (_ + 3168) _ => exact UW
             end.
        all: try eassumption. all: try (unfold AIMG_HI; lia). all: try (Z.div_mod_to_equations; lia).
        all: match goal with |- ?G => idtac "REMU" G end. }

  cbv beta. intros ms2 PU. unfold unwind_impl_post in PU.
  (nd_pre PU 18%nat; intros t0b t1b t2b a0b a1b a2b a3b a4b a5b a6b a7b t3b t4b t5b t6b m2 tb2 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 10%nat; intros MUu WMu MIu STu SZ2 TB2 LTB2 TRF2 BP2 UW2; nd_post).
  unname_sp. rewrite ?unsigned_lit in MUu by lia. rewrite ?unsigned_lit in STu by lia.
  replace (ret_pc (Z_to_bv 64 353400)) with (Z_to_bv 64 353400) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (icptB_spec RNG); [exact STu | atop_facts; lia | lia | exact MIu | reflexivity | exact RIMG | exact RTLS | solve_rng]. }
  cbv beta. intros ms3 PB. unfold icptB_post in PB. (nd_pre PB 2%nat; intros m3 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 5%nat; intros MUb WMb MIb STb FR16; nd_post).
  (* [comment removed for export] *)
  assert (MU3 : munch [(bv_unsigned sp - 2288, bv_unsigned sp); (t + 3168, t + 3169)]%Z m m3).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUb]]. eapply munch_trans; [| eapply munch_weaken; [| exact MUu]].
    eapply munch_weaken; [| exact MUa]. all: unfold sub_fp; cbn [outside]; intros q Hq; lia. }
  assert (WM3 : wmono asegs m m3). { eapply wmono_trans; [| exact WMb]. eapply wmono_trans; [exact WMa | exact WMu]. }
  assert (MU13 : munch [(bv_unsigned sp - 2288, bv_unsigned sp - 2128); (bv_unsigned sp - 2120, bv_unsigned sp - 2116); (bv_unsigned sp - 2112, bv_unsigned sp - 64); (t + 3168, t + 3169)]%Z m1 m3).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUb]]. eapply munch_weaken; [| exact MUu].
    all: unfold sub_fp; cbn [outside]; intros q Hq; lia. }
  assert (WM13 : wmono asegs m1 m3). { eapply wmono_trans; [exact WMu | exact WMb]. }
  xport INI MU13 WM13 ltac:(lia). xport TI MU13 WM13 ltac:(lia). xport TK MU13 WM13 ltac:(lia). xport T88 MU13 WM13 ltac:(lia).
  xport TSD MU13 WM13 ltac:(lia). xport CT MU13 WM13 ltac:(ub CT2; lia). xport FRp MU13 WM13 ltac:(lia). xport TAG MU13 WM13 ltac:(lia).
  xport REST MU13 WM13 ltac:(lia).
  xport RSS MU3 WM3 ltac:(lia). xport IMAX MU3 WM3 ltac:(lia).
  (* [comment removed for export] *)
  xport SZ2 MUb WMb ltac:(lia). replace (bv_unsigned sp - 2128 + 8) with (bv_unsigned sp + -2120) in SZ2 by lia.
  rw_join SZ2 TAG SZT. apply rw_cells_C4C4_to_C8 in SZT. 2: { cbn [length app]; clear -LTRC; lia. }
  rw_join FRp SZT SS.
  xport TB2 MUb WMb ltac:(rewrite LTB2; lia). xport BP2 MUb WMb ltac:(lia). xport UW2 MUb WMb ltac:(lia).
  rewrite Z_to_bv_bv_unsigned in BP2. rw_join BP2 REST FRS.
  replace (bv_unsigned sp - 2128 + 2056) with (bv_unsigned sp + -72) in FRS by lia.
  (* [comment removed for export] *)
  name_sp sp (-2144).
  step.                                                          (* [comment removed for export] *)
  eapply evtF_mono.
  { eapply (allocA_pre_spec_sec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m3 n (bv_unsigned sp + -2128) (al_ctx L) t lo).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => rewrite Hsp; exact STb
         | |- mem_inv _ _ => exact MIb
         | |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => assumption | |- _ /\ _ => split end)
         | |- @eq word _ _ => first [reflexivity | exact TP]
         | |- _ \/ _ => unboxed CT2
         end.
    all: try lazymatch goal with |- rng _ _ _ => solve_rng end.
    all: try eassumption. all: try (unfold AIMG_HI; lia).
    all: match goal with |- ?G => idtac "REMAL" G end. }
  cbv beta. intros ms4 PL. unfold allocA_pre_postS in PL.
  (nd_pre PL 13%nat; intros t0c t1c t2c a4c a5c a6c a7c t3c t4c t5c t6c m4 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 5%nat; intros MUl WMl MIl STl [fr0 FRa]; nd_post).
  rewrite ?Hsp in MUl. rewrite ?Hsp in STl. rewrite ?Hsp in FRa.
  xport FR16 MUl WMl ltac:(lia). xport SS MUl WMl ltac:(lia). xport UW2 MUl WMl ltac:(lia). xport FRS MUl WMl ltac:(lia).
  xport TB2 MUl WMl ltac:(rewrite LTB2; lia).
  unfold malloc_pre_postS. lazymatch type of Hsp with bv_unsigned ?spx = _ => exists spx end. do 11 eexists. do 7 eexists. exists fr0, junk2, tb2, m4.
  split; [reflexivity|]. split; [clear -Hsp; lia|].
  split.
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUl]]. eapply munch_weaken; [| exact MU3].
    all: unfold sub_fp; cbn [outside]; intros q Hq; lia. }
  split; [eapply wmono_trans; [exact WM3 | exact WMl]|]. split; [exact MIl|].
  split; [replace (bv_unsigned sp - 2272) with (bv_unsigned sp + -2144 - 128) by lia; exact STl|].
  split; [replace (bv_unsigned sp - 2272) with (bv_unsigned sp + -2144 - 128) by lia; exact FRa|].
  split; [exact FR16|].
  replace (bv_unsigned sp + -2112) with (bv_unsigned sp + -2128 + 16) in SS by lia.
  replace (bv_unsigned sp - 2128 + 16) with (bv_unsigned sp + -2128 + 16) in TB2 by lia.
  split; [exact SS|]. split; [exact TB2|]. split; [exact LTB2|]. split; [exact TRF2|]. split; [exact FRS|]. exact UW2.
  Unshelve. all: try exact STb; try exact STa; try exact STu.
Qed.
End Zd1.
#[using="Type"] Lemma malloc_pre_spec_sec : ltac:(let t := eval cbv delta [malloc_pre_spec_sec__stmt] in malloc_pre_spec_sec__stmt in exact t).
Proof. exact malloc_pre_spec_sec__body. Qed.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc1b__A3W.F_aalloc1b.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc1b__A3W.F_aalloc1s.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aunwind.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc1b__A3W.F_aunwind2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_amalloc_iseg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc__A3W.F_amalloc_icpt.TwB.
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


(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition malloc_pre_postS (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (n t lo : Z) (trc : list Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (spA : word) t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 (s0A s1A s2A s3A s4A s5A s0i : word) (fr0 junk2 : list byte) (tb : list word) m',
    ms' = MS (mkR (Z_to_bv 64 0x33f10) (Z_to_bv 64 (bv_unsigned spA + -128)) gp tp t0 t1 t2
                  (Z_to_bv 64 0) (Z_to_bv 64 n)
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 (t + 208)) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 8) a4 a5 a6 a7
                  (Z_to_bv 64 8) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n)
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 t) (Z_to_bv 64 1)
                  t3 t4 t5 t6)
             F (Z_to_bv 64 0x383f0) fc None m' (seg_rom asegs)
    /\ bv_unsigned spA = bv_unsigned sp - 2144
    /\ munch [(bv_unsigned sp - 2320, bv_unsigned sp); (t + 3168, t + 3169)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp - 2272)
    /\ rw_cells asegs m' (bv_unsigned sp - 2272)
         [CB 8 fr0; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 16); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5A;
          C8 s4A; C8 s3A; C8 s2A; C8 s1A; C8 s0A; C8 (Z_to_bv 64 0x33c40)]
    /\ rw_cells asegs m' (bv_unsigned sp + -2144) [C8 s0i; C8 (Z_to_bv 64 0x564f0)]
    /\ rw_cells asegs m' (bv_unsigned sp + -2128) [C8 (Z_to_bv 64 (bv_unsigned sp + -2128 + 16)); C8 (Z_to_bv 64 (1 + Z.of_nat (length trc)))]
    /\ u64arr asegs m' (bv_unsigned sp + -2128 + 16) tb /\ length tb = 255%nat
    /\ map bv_unsigned (firstn (Datatypes.S (length trc)) tb) = AMALLOC_PC :: trc
    /\ rw_cells asegs m' (bv_unsigned sp + -72) [C8 sp; CB 8 junk2; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' (t + 3168) [C1 (Z_to_bv 8 0)].

Definition malloc_pre_spec_sec__stmt : Prop := forall (L : alayout) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n t lo top bot : Z) (tr trc : list Z),
  let ctx := al_ctx L in
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 n -> 1 <= n <= AREQMAX -> is_primary n = false ->
  bv_unsigned sp mod 16 = 0 ->
  (* [comment removed for export] *)
  allocA_cells m ctx t -> poison_cells m ->
  rw_cells asegs m 0xaf6fc [C4 (Z_to_bv 64 30)] ->
  rw_cells asegs m 0x14054a [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m GOT_PGSZ [C8 (Z_to_bv 64 APGSZ)] -> rw_cells asegs m APGSZ [C8 (Z_to_bv 64 4096)] ->
  (* [comment removed for export] *)
  rw_cells asegs m (ctx + 8) [C4 (Z_to_bv 64 0)] -> rw_cells asegs m t [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (t + 8) [C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)] ->
  rw_cells asegs m (t + 40) [C1 (Z_to_bv 8 0)] -> rw_cells asegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> sclr ctx 65536 ->
  iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> t mod 4096 = 0 -> sclr t 4096 ->
  (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  (* [comment removed for export] *)
  (bv_unsigned sp + 16 < top /\ uchain m top AMALLOC_PC (bv_unsigned sp) (bv_unsigned s0) 28%nat tr /\ (length tr <= 28)%nat /\ trc = bv_unsigned ra :: tr
   /\ rng RNG lo (top - lo))
  \/ (top <= bv_unsigned sp + 16 /\ bv_unsigned sp < 2^47 /\ trc = []) ->
  bv_unsigned s0 <> bv_unsigned sp + 8 ->
  0 <= bot -> bot < bv_unsigned sp -> bot + 4096 <= top -> top <= 2^47 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AMALLOC_PC ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  evtF asegs RNG (malloc_pre_postS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n t lo trc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AMALLOC_SYM) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 5).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 6).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 7).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 8).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 9).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 10).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 11).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 12).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 13).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 14).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 15).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 16).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 17).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 18).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 19).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 20).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 21).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 22).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 23).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 24).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 25).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 26).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 27).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 28).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 29).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 30).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 31).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 32).
Variable F : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 33).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 34).
Variable m : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 35).
Variable n : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 36).
Variable t : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 37).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 38).
Variable top : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 39).
Variable bot : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 40).
Variable tr : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 41).
Variable trc : ltac2:(SecDietF.SzSecF.ty 'malloc_pre_spec_sec__stmt 42).
#[using="Type"] Lemma malloc_pre_spec_sec__body : ltac:(let T := type of (fun (h : malloc_pre_spec_sec__stmt) => h L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n t lo top bot tr trc) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (n, (t, (lo, (top, (bot, (tr, trc))))))))))))))))))))))))))))))))))))))))))) as _.
 cbv zeta.
  intros ST CEIL LO MI TP Ha0 N PRIM SP16 AC PC LS1 CT8 GPG PGC CX8 TT0 TT SW UW CX0 CX1 CXS T0 T1 TAL TS CT2
         ARM S0NE B0 BB BTOP TOP RA4 RANE RIMG RTLS RSTK RCTX RT. band_lin.   (* [comment removed for export] *)
  assert (LTRC : (length trc <= 29)%nat) by (destruct ARM as [(_ & _ & L1 & -> & _)|(_ & _ & ->)]; cbn [length]; lia).
  assert (SP47 : bv_unsigned sp < 2^47) by (destruct ARM as [(X1 & _)|(_ & X2 & _)]; lia).
  pose proof AC as AC'. (nd_pre AC' 8%nat; intros INI RSS IMAX TI TK T88 TSD CT; nd_post).
  unfold AIMG_HI, AINSTANCE, ATP88, ATSD, ATSDI, ATSDK, AINITED, ARSSLIM, GOT_PGSZ, APGSZ, AMALLOC_SYM, AMALLOC_PC in *.
  word_range sp SPR. word_range s0 S0R. word_range ra RAR.
  (pose proof (sec_facts n N PRIM) as ndP__; nd_pre ndP__ 10%nat; intros NB RZ RSE RSR RSM NSE MSE MSR MSM MSB; nd_post).
  box CT2.
  (nd_pre PC 7%nat; intros GOT GOT80 REAL PC4 PC5 PC6 PC7; nd_post).
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (icptA_spec RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n lo);
      try eassumption; try lia; try solve_rng. }
  cbv beta. intros ms1 PA. unfold icptA_post in PA.
  (nd_pre PA 13%nat; intros t0a t1a t2a a6a a7a t3a t4a t5a t6a m1 junk1 junk2 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 7%nat; intros MUa WMa MIa STa FRA FRt FRs; nd_post).
  (* [comment removed for export] *)
  pose proof FRs as FRs0. rw_split FRs0 7%nat FRsx FRsr. clear FRsx.
  destruct FRsr as [[_ BSR] _]. cbn [cells_bytes cbytes app] in BSR. rewrite app_nil_r in BSR.
  apply bytes_at_app in BSR. destruct BSR as [BS0 BRA]. rewrite length_le8 in BRA.
  replace (bv_unsigned sp + -16 + Z.of_nat 8) with (bv_unsigned sp - 8) in BRA by lia.
  replace (bv_unsigned sp + -16) with (bv_unsigned sp - 16) in BS0 by lia.
  (* [comment removed for export] *)
  xport TI MUa WMa ltac:(lia). xport TK MUa WMa ltac:(lia). xport T88 MUa WMa ltac:(lia). xport TSD MUa WMa ltac:(lia).
  xport CT MUa WMa ltac:(lia). xport GPG MUa WMa ltac:(lia). xport PGC MUa WMa ltac:(lia). xport TT MUa WMa ltac:(lia).
  xport SW MUa WMa ltac:(lia). xport UW MUa WMa ltac:(lia). xport INI MUa WMa ltac:(lia).
  pose proof FRA as FRA0. rw_split FRA0 1%nat FRp FRz. rw_split FRz 1%nat SZC TAG.
  change 2040%nat with (8 * 255)%nat in FRt. destruct (u64arr_of_CB _ _ 255%nat _ FRt) as [TB LTB].
  pose proof FRs as FRs1. rw_split FRs1 1%nat BPJ REST.
  replace (bv_unsigned sp + -2120) with (bv_unsigned sp - 2128 + 8) in SZC by lia.
  replace (bv_unsigned sp + -2112) with (bv_unsigned sp - 2128 + 16) in TB by lia.
  replace (bv_unsigned sp + -72) with (bv_unsigned sp - 2128 + 2056) in BPJ by lia.
  (* [comment removed for export] *)
  step.                                                          (* [comment removed for export] *)
  name_sp sp (-2128).
  eapply evtF_cut with (P := unwind_impl_post (bv_unsigned sp - 2128) 353412 (bv_unsigned sp) t _ _ gp tp _ _ _ _ _ _ s6 s7 s8 s9 s10 s11 F fc lo trc m1).
  { destruct ARM as [(BT & UC & LTR & Etrc & RTOP)|(BT & BT2 & Etrc)]; rewrite Etrc.
    - (* [comment removed for export] *)
      assert (UC1 : uchain m1 top 353412 bot (bv_unsigned sp) 29%nat ([bv_unsigned ra] ++ tr)).
      { replace ([bv_unsigned ra] ++ tr) with ((if bv_unsigned ra =? 353412 then [] else [bv_unsigned ra]) ++ tr)
          by (replace (bv_unsigned ra =? 353412) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
        eapply (uc_step m1 top 353412 bot (bv_unsigned sp) 29%nat (bv_unsigned s0) (bv_unsigned ra) tr); try lia.
        - rewrite Z_to_bv_bv_unsigned. exact BS0.
        - rewrite Z_to_bv_bv_unsigned. exact BRA.
        - replace (bv_unsigned ra =? 353412) with false by (symmetry; apply Z.eqb_neq; lia). cbn [Nat.pred].
          destruct (Z_le_gt_dec (bv_unsigned sp + 16) (bv_unsigned s0)) as [GE|LT].
          + eapply uchain_frame; [exact UC|]. intros a Ha. apply MUa. cbn [outside]. rewrite unsigned_lit by lia. split; [lia| exact I].
          + inversion UC; subst; [apply uc_stop; assumption | exfalso | exfalso]; Z.div_mod_to_equations; lia. }
      clear BS0 BRA UC.
      change (bv_unsigned ra :: tr) with ([bv_unsigned ra] ++ tr).
    eapply (unwind_impl_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (bv_unsigned sp - 2128) 353412 (bv_unsigned sp) (al_ctx L) t top bot lo (words_of_bytes junk1) ([bv_unsigned ra] ++ tr)).
        all: try lazymatch goal with
             | |- stk _ _ _ _ => rewrite Hsp; exact STa
             | |- mem_inv _ _ => exact MIa
             | |- @eq word _ _ => first [reflexivity | exact TP | rewrite Z_to_bv_bv_unsigned; reflexivity | apply Z_to_bv_eqm; rewrite ?unsigned_lit by lia; lia]
             | |- ex _ => first [eexists; exact SZC | eexists; exact BPJ]
             | |- u64arr _ _ _ _ => exact TB
             | |- uchain _ _ _ _ _ _ _ => exact UC1
             | |- _ \/ _ => unboxed CT2
             | |- rng _ _ _ => solve_rng
             | |- rw_cells _ _ (_ + 152) _ => exact CT
             | |- rw_cells _ _ (_ + 8) [C8 _; C8 _] => exact TT
             | |- rw_cells _ _ (_ + 40) _ => exact SW
             | |- rw_cells _ _ (_ + 3168) _ => exact UW
             end.
        all: try eassumption. all: try (unfold AIMG_HI; lia). all: try (Z.div_mod_to_equations; lia).
        all: match goal with |- ?G => idtac "REMU" G end.
    - (* [comment removed for export] *)
      clear BS0 BRA.
    eapply (unwind_impl_spec0 RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (bv_unsigned sp - 2128) 353412 (bv_unsigned sp) (al_ctx L) t top bot lo (words_of_bytes junk1)).
        all: try lazymatch goal with
             | |- stk _ _ _ _ => rewrite Hsp; exact STa
             | |- mem_inv _ _ => exact MIa
             | |- @eq word _ _ => first [reflexivity | exact TP | rewrite Z_to_bv_bv_unsigned; reflexivity | apply Z_to_bv_eqm; rewrite ?unsigned_lit by lia; lia]
             | |- ex _ => first [eexists; exact SZC | eexists; exact BPJ]
             | |- u64arr _ _ _ _ => exact TB
             | |- uchain _ _ _ _ _ _ _ => exact UC1
             | |- _ \/ _ => unboxed CT2
             | |- rng _ _ _ => solve_rng
             | |- rw_cells _ _ (_ + 152) _ => exact CT
             | |- rw_cells _ _ (_ + 8) [C8 _; C8 _] => exact TT
             | |- rw_cells _ _ (_ + 40) _ => exact SW
             | |- rw_cells _ _ (_ + 3168) _ => exact UW
             end.
        all: try eassumption. all: try (unfold AIMG_HI; lia). all: try (Z.div_mod_to_equations; lia).
        all: match goal with |- ?G => idtac "REMU" G end. }

  cbv beta. intros ms2 PU. unfold unwind_impl_post in PU.
  (nd_pre PU 18%nat; intros t0b t1b t2b a0b a1b a2b a3b a4b a5b a6b a7b t3b t4b t5b t6b m2 tb2 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 10%nat; intros MUu WMu MIu STu SZ2 TB2 LTB2 TRF2 BP2 UW2; nd_post).
  unname_sp. rewrite ?unsigned_lit in MUu by lia. rewrite ?unsigned_lit in STu by lia.
  replace (ret_pc (Z_to_bv 64 353504)) with (Z_to_bv 64 353504) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (icptB_spec RNG); [exact STu | atop_facts; lia | lia | exact MIu | reflexivity | exact RIMG | exact RTLS | solve_rng]. }
  cbv beta. intros ms3 PB. unfold icptB_post in PB. (nd_pre PB 2%nat; intros m3 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 5%nat; intros MUb WMb MIb STb FR16; nd_post).
  (* [comment removed for export] *)
  assert (MU3 : munch [(bv_unsigned sp - 2288, bv_unsigned sp); (t + 3168, t + 3169)]%Z m m3).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUb]]. eapply munch_trans; [| eapply munch_weaken; [| exact MUu]].
    eapply munch_weaken; [| exact MUa]. all: unfold sub_fp; cbn [outside]; intros q Hq; lia. }
  assert (WM3 : wmono asegs m m3). { eapply wmono_trans; [| exact WMb]. eapply wmono_trans; [exact WMa | exact WMu]. }
  assert (MU13 : munch [(bv_unsigned sp - 2288, bv_unsigned sp - 2128); (bv_unsigned sp - 2120, bv_unsigned sp - 2116); (bv_unsigned sp - 2112, bv_unsigned sp - 64); (t + 3168, t + 3169)]%Z m1 m3).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUb]]. eapply munch_weaken; [| exact MUu].
    all: unfold sub_fp; cbn [outside]; intros q Hq; lia. }
  assert (WM13 : wmono asegs m1 m3). { eapply wmono_trans; [exact WMu | exact WMb]. }
  xport INI MU13 WM13 ltac:(lia). xport TI MU13 WM13 ltac:(lia). xport TK MU13 WM13 ltac:(lia). xport T88 MU13 WM13 ltac:(lia).
  xport TSD MU13 WM13 ltac:(lia). xport CT MU13 WM13 ltac:(ub CT2; lia). xport FRp MU13 WM13 ltac:(lia). xport TAG MU13 WM13 ltac:(lia).
  xport REST MU13 WM13 ltac:(lia).
  xport RSS MU3 WM3 ltac:(lia). xport IMAX MU3 WM3 ltac:(lia).
  (* [comment removed for export] *)
  xport SZ2 MUb WMb ltac:(lia). replace (bv_unsigned sp - 2128 + 8) with (bv_unsigned sp + -2120) in SZ2 by lia.
  rw_join SZ2 TAG SZT. apply rw_cells_C4C4_to_C8 in SZT. 2: { cbn [length app]; clear -LTRC; lia. }
  rw_join FRp SZT SS.
  xport TB2 MUb WMb ltac:(rewrite LTB2; lia). xport BP2 MUb WMb ltac:(lia). xport UW2 MUb WMb ltac:(lia).
  rewrite Z_to_bv_bv_unsigned in BP2. rw_join BP2 REST FRS.
  replace (bv_unsigned sp - 2128 + 2056) with (bv_unsigned sp + -72) in FRS by lia.
  (* [comment removed for export] *)
  name_sp sp (-2144).
  step.                                                          (* [comment removed for export] *)
  eapply evtF_mono.
  { eapply (allocA_pre_spec_sec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m3 n (bv_unsigned sp + -2128) (al_ctx L) t lo).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => rewrite Hsp; exact STb
         | |- mem_inv _ _ => exact MIb
         | |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => assumption | |- _ /\ _ => split end)
         | |- @eq word _ _ => first [reflexivity | exact TP]
         | |- _ \/ _ => unboxed CT2
         end.
    all: try lazymatch goal with |- rng _ _ _ => solve_rng end.
    all: try eassumption. all: try (unfold AIMG_HI; lia).
    all: match goal with |- ?G => idtac "REMAL" G end. }
  cbv beta. intros ms4 PL. unfold allocA_pre_postS in PL.
  (nd_pre PL 13%nat; intros t0c t1c t2c a4c a5c a6c a7c t3c t4c t5c t6c m4 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 5%nat; intros MUl WMl MIl STl [fr0 FRa]; nd_post).
  rewrite ?Hsp in MUl. rewrite ?Hsp in STl. rewrite ?Hsp in FRa.
  xport FR16 MUl WMl ltac:(lia). xport SS MUl WMl ltac:(lia). xport UW2 MUl WMl ltac:(lia). xport FRS MUl WMl ltac:(lia).
  xport TB2 MUl WMl ltac:(rewrite LTB2; lia).
  unfold malloc_pre_postS. lazymatch type of Hsp with bv_unsigned ?spx = _ => exists spx end. do 11 eexists. do 7 eexists. exists fr0, junk2, tb2, m4.
  split; [reflexivity|]. split; [clear -Hsp; lia|].
  split.
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUl]]. eapply munch_weaken; [| exact MU3].
    all: unfold sub_fp; cbn [outside]; intros q Hq; lia. }
  split; [eapply wmono_trans; [exact WM3 | exact WMl]|]. split; [exact MIl|].
  split; [replace (bv_unsigned sp - 2272) with (bv_unsigned sp + -2144 - 128) by lia; exact STl|].
  split; [replace (bv_unsigned sp - 2272) with (bv_unsigned sp + -2144 - 128) by lia; exact FRa|].
  split; [exact FR16|].
  replace (bv_unsigned sp + -2112) with (bv_unsigned sp + -2128 + 16) in SS by lia.
  replace (bv_unsigned sp - 2128 + 16) with (bv_unsigned sp + -2128 + 16) in TB2 by lia.
  split; [exact SS|]. split; [exact TB2|]. split; [exact LTB2|]. split; [exact TRF2|]. split; [exact FRS|]. exact UW2.
  Unshelve. all: try exact STb; try exact STa; try exact STu.
Qed.
End Zd1.
#[using="Type"] Lemma malloc_pre_spec_sec : ltac:(let t := eval cbv delta [malloc_pre_spec_sec__stmt] in malloc_pre_spec_sec__stmt in exact t).
Proof. exact malloc_pre_spec_sec__body. Qed.
End CANSEC1.
End TwB.
End F_amalloc_preS.

(* [comment removed for export] *)
Module F_arealloc_pre.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecSlog__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc1b__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aunwind. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc1b__A3W.F_aalloc1b OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aunwind OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc1b__A3W.F_aunwind2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc__A3W.F_amalloc_icpt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3g0__A3W.F_arealloc_iseg.
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



(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Notation realloc_pre_W sp t :=
  ([(bv_unsigned sp - 2368, bv_unsigned sp); (0xaf800, 0xaf800 + 0x81030); (0x13e088, 0x13e088 + 4); (t + 3168, t + 3169);
    (t + 2800, t + 2800 + 368)]%Z) (only parsing).

Definition realloc_pre_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (p n t lo : Z) (trc : list Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a7 t3 t4 t5 t6 (fr0 junk0 junk2 : list byte) (tb sj' : list word) m',
    ms' = MS (mkR (Z_to_bv 64 0x34788) (Z_to_bv 64 (bv_unsigned sp + -2208)) gp tp t0 t1 t2
                  (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 p)
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 n) (Z_to_bv 64 8) (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 1) (Z_to_bv 64 1)
                  (Z_to_bv 64 (bv_unsigned sp + -2136)) a7
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 n) (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 (bv_unsigned sp + -89))
                  s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x33c08) fc None m' (seg_rom asegs)
    /\ munch (realloc_pre_W sp t) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -2208)
    /\ rw_cells asegs m' (bv_unsigned sp + -2208) [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 0x568f0); C8 (Z_to_bv 64 p); C8 (Z_to_bv 64 n); C8 sp; C8 (Z_to_bv 64 0x3470c)]
    /\ rw_cells asegs m' (bv_unsigned sp + -2160) [CB 8 fr0; C8 (Z_to_bv 64 0x56960)]
    /\ rw_cells asegs m' (bv_unsigned sp + -2144) [CB 8 junk0]
    /\ rw_cells asegs m' (bv_unsigned sp + -2136) [C8 (Z_to_bv 64 (bv_unsigned sp + -2136 + 16)); C4 (Z_to_bv 64 (1 + Z.of_nat (length trc))); C4 (Z_to_bv 64 0)]
    /\ u64arr asegs m' (bv_unsigned sp + -2136 + 16) tb /\ length tb = 255%nat
    /\ map bv_unsigned (firstn (Datatypes.S (length trc)) tb) = AREALLOC_PC' :: trc
    /\ rw_cells asegs m' (bv_unsigned sp + -80) [C8 sp; CB 8 junk2; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' (t + 3168) [C1 (Z_to_bv 8 0)]
    /\ u64arr asegs m' (t + 2800) sj' /\ length sj' = 46%nat
    /\ rw_cells asegs m' 0x13e088 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ stk asegs m' 0xaf800 (0xaf800 + 0x81030)
    /\ (forall j, 0 <= j < 32768 -> bytes_at asegs m' (0xaf808 + 8 * j) (le8 (Z_to_bv 64 0))).

Definition realloc_pre_spec__stmt : Prop := forall (L : alayout) (ia : bool) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (p n t lo top bot : Z) (tr trc : list Z) (sj : list word),
  let ctx := al_ctx L in
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 n -> 1 <= p < 2^47 -> 1 <= n < 2^64 ->
  bv_unsigned sp mod 16 = 0 ->
  (* [comment removed for export] *)
  allocA_cells m ctx t ->
  rw_cells asegs m 0xa54a0 [C8 (Z_to_bv 64 0x140128); C8 (Z_to_bv 64 0xabdf8); C8 (Z_to_bv 64 0xae5f8);
                             C8 (Z_to_bv 64 0xaf2e8); C8 (Z_to_bv 64 0xaf2f0); C8 (Z_to_bv 64 0xaf2e0)] ->
  rw_cells asegs m 0xaf2fc [C4 (Z_to_bv 64 30)] ->
  rw_cells asegs m 0x14014a [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m GOT_PGSZ [C8 (Z_to_bv 64 APGSZ)] -> rw_cells asegs m APGSZ [C8 (Z_to_bv 64 4096)] ->
  rw_cells asegs m 0xa5490 [C8 (Z_to_bv 64 0x13e0a0)] -> rw_cells asegs m 0x13e0a0 [C8 (Z_to_bv 64 4096)] ->
  (* [comment removed for export] *)
  rw_cells asegs m AIA_FLAG [C1 (Z_to_bv 8 (if ia then 1 else 0)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  stk asegs m AIA_BASE (AIA_BASE + AIA_SIZE) ->
  (ia = true -> forall j, 0 <= j < 32768 -> bytes_at asegs m (AIA_MAP1 + 8 * j) (le8 (Z_to_bv 64 0))) ->
  (* [comment removed for export] *)
  rw_cells asegs m (ctx + 8) [C4 (Z_to_bv 64 0)] -> rw_cells asegs m t [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (t + 8) [C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)] ->
  rw_cells asegs m (t + 40) [C1 (Z_to_bv 8 0)] -> rw_cells asegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> sclr ctx 65536 ->
  iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> t mod 4096 = 0 -> sclr t 4096 ->
  (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  (* [comment removed for export] *)
  (bv_unsigned sp + 16 < top /\ uchain m top AREALLOC_PC' (bv_unsigned sp) (bv_unsigned s0) 28%nat tr /\ (length tr <= 28)%nat /\ trc = bv_unsigned ra :: tr
   /\ rng RNG lo (top - lo))
  \/ (top <= bv_unsigned sp + 16 /\ bv_unsigned sp < 2^47 /\ trc = []) ->
  bv_unsigned s0 <> bv_unsigned sp + 8 ->
  0 <= bot -> bot < bv_unsigned sp -> bot + 4096 <= top -> top <= 2^47 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AREALLOC_PC' ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  evtF asegs RNG (realloc_pre_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc p n t lo trc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AREALLOC_SYM') fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 0).
Variable ia : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 1).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 2).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 3).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 4).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 5).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 6).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 7).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 8).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 9).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 10).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 11).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 12).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 13).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 14).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 15).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 16).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 17).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 18).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 19).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 20).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 21).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 22).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 23).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 24).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 25).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 26).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 27).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 28).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 29).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 30).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 31).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 32).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 33).
Variable F : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 34).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 35).
Variable m : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 36).
Variable p : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 37).
Variable n : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 38).
Variable t : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 39).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 40).
Variable top : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 41).
Variable bot : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 42).
Variable tr : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 43).
Variable trc : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 44).
Variable sj : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 45).
#[using="Type"] Lemma realloc_pre_spec__body : ltac:(let T := type of (fun (h : realloc_pre_spec__stmt) => h L ia RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p n t lo top bot tr trc sj) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (ia, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (p, (n, (t, (lo, (top, (bot, (tr, (trc, sj)))))))))))))))))))))))))))))))))))))))))))))) as _.
 cbv zeta.
  intros ST CEIL LO MI TP Ha0 Ha1 PR NR SP16 AC GOT LS1 CT8 GPG PGC PG1 PG2 FL IAS IAM CX8 TT0 TT SW UW STATS LSJ CX0 CX1 CXS T0 T1 TAL TS CT2
         ARM S0NE B0 BB BTOP TOP RA4 RANE RIMG RTLS RSTK RCTX RT.
  pose proof T0 as T0i. band_lin.   (* [comment removed for export] *)
  assert (LTRC : (length trc <= 29)%nat) by (destruct ARM as [(_ & _ & L1 & -> & _)|(_ & _ & ->)]; cbn [length]; lia).
  assert (SP47 : bv_unsigned sp < 2^47) by (destruct ARM as [(X1 & _)|(_ & X2 & _)]; lia).
  pose proof AC as AC'. (nd_pre AC' 8%nat; intros INI RSS IMAX TI TK T88 TSD CT; nd_post).
  unfold AIMG_HI, AINSTANCE, ATP88, ATSD, ATSDI, ATSDK, AINITED, ARSSLIM, GOT_PGSZ, APGSZ, AREALLOC_PC', AIA_FLAG, AIA_BASE, AIA_SIZE, AIA_MAP1 in *.
  word_range sp SPR. word_range s0 S0R. word_range ra RAR.
  box CT2.
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (ricptA_spec ia RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p n lo);
      try eassumption; try lia; try solve_rng. }
  cbv beta. intros ms1 PA. unfold ricptA_post in PA.
  (nd_pre PA 14%nat; intros t0a t1a t2a a6a a7a t3a t4a t5a t6a m1 junk0 junk1 junk2 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 11%nat; intros MUa WMa MIa STa FRP FRA FRt FRs FL1 IAS1 IAM1; nd_post).
  (* [comment removed for export] *)
  pose proof FRs as FRs0. rw_split FRs0 8%nat FRsx FRsr. clear FRsx.
  destruct FRsr as [[_ BSR] _]. cbn [cells_bytes cbytes app] in BSR. rewrite app_nil_r in BSR.
  apply bytes_at_app in BSR. destruct BSR as [BS0 BRA]. rewrite length_le8 in BRA.
  replace (bv_unsigned sp + -16 + Z.of_nat 8) with (bv_unsigned sp - 8) in BRA by lia.
  replace (bv_unsigned sp + -16) with (bv_unsigned sp - 16) in BS0 by lia.
  (* [comment removed for export] *)
  xport TI MUa WMa ltac:(lia). xport TK MUa WMa ltac:(lia). xport T88 MUa WMa ltac:(lia). xport TSD MUa WMa ltac:(lia).
  xport CT MUa WMa ltac:(lia). xport GPG MUa WMa ltac:(lia). xport PGC MUa WMa ltac:(lia). xport TT MUa WMa ltac:(lia).
  xport SW MUa WMa ltac:(lia). xport UW MUa WMa ltac:(lia). xport INI MUa WMa ltac:(lia).
  xport STATS MUa WMa ltac:(rewrite LSJ; lia).
  pose proof FRA as FRA0. rw_split FRA0 1%nat FRp FRz. rw_split FRz 1%nat SZC TAG.
  change 2040%nat with (8 * 255)%nat in FRt. destruct (u64arr_of_CB _ _ 255%nat _ FRt) as [TB LTB].
  pose proof FRs as FRs1. rw_split FRs1 1%nat BPJ REST.
  replace (bv_unsigned sp + -2128) with (bv_unsigned sp - 2136 + 8) in SZC by lia.
  replace (bv_unsigned sp + -2120) with (bv_unsigned sp - 2136 + 16) in TB by lia.
  replace (bv_unsigned sp + -80) with (bv_unsigned sp - 2136 + 2056) in BPJ by lia.
  (* [comment removed for export] *)
  step.                                                          (* [comment removed for export] *)
  name_sp sp (-2144).
  eapply evtF_cut with (P := unwind_impl_post (bv_unsigned sp - 2136) 354544 (bv_unsigned sp) t _ _ gp tp _ _ _ _ _ _ _ s7 s8 s9 s10 s11 F fc lo trc m1).
  { destruct ARM as [(BT & UC & LTR & Etrc & RTOP)|(BT & BT2 & Etrc)]; rewrite Etrc.
    - (* [comment removed for export] *)
      assert (UC1 : uchain m1 top 354544 bot (bv_unsigned sp) 29%nat ([bv_unsigned ra] ++ tr)).
      { replace ([bv_unsigned ra] ++ tr) with ((if bv_unsigned ra =? 354544 then [] else [bv_unsigned ra]) ++ tr)
          by (replace (bv_unsigned ra =? 354544) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
        eapply (uc_step m1 top 354544 bot (bv_unsigned sp) 29%nat (bv_unsigned s0) (bv_unsigned ra) tr); try lia.
        - rewrite Z_to_bv_bv_unsigned. exact BS0.
        - rewrite Z_to_bv_bv_unsigned. exact BRA.
        - replace (bv_unsigned ra =? 354544) with false by (symmetry; apply Z.eqb_neq; lia). cbn [Nat.pred].
          destruct (Z_le_gt_dec (bv_unsigned sp + 16) (bv_unsigned s0)) as [GE|LT].
          + eapply uchain_frame; [exact UC|]. intros a Ha. apply MUa. cbn [outside]. rewrite unsigned_lit by lia. pose proof atop_range as ATR9. split; [lia|]. split; [lia|]. split; [lia| exact I].
          + inversion UC; subst; [apply uc_stop; assumption | exfalso | exfalso]; Z.div_mod_to_equations; lia. }
      clear BS0 BRA UC.
      change (bv_unsigned ra :: tr) with ([bv_unsigned ra] ++ tr).
    eapply (unwind_impl_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (bv_unsigned sp - 2136) 354544 (bv_unsigned sp) (al_ctx L) t top bot lo (words_of_bytes junk1) ([bv_unsigned ra] ++ tr)).
        all: try lazymatch goal with
             | |- stk _ _ _ _ => rewrite Hsp; exact STa
             | |- mem_inv _ _ => exact MIa
             | |- @eq word _ _ => first [reflexivity | exact TP | rewrite Z_to_bv_bv_unsigned; reflexivity | apply Z_to_bv_eqm; rewrite ?unsigned_lit by lia; lia]
             | |- ex _ => first [eexists; exact SZC | eexists; exact BPJ]
             | |- u64arr _ _ _ _ => exact TB
             | |- uchain _ _ _ _ _ _ _ => exact UC1
             | |- _ \/ _ => unboxed CT2
             | |- rng _ _ _ => solve_rng
             | |- rw_cells _ _ (_ + 152) _ => exact CT
             | |- rw_cells _ _ (_ + 8) [C8 _; C8 _] => exact TT
             | |- rw_cells _ _ (_ + 40) _ => exact SW
             | |- rw_cells _ _ (_ + 3168) _ => exact UW
             end.
        all: try eassumption. all: try (unfold AIMG_HI; lia). all: try (Z.div_mod_to_equations; lia).
        all: match goal with |- ?G => idtac "REMU" G end.
    - (* [comment removed for export] *)
      clear BS0 BRA.
    eapply (unwind_impl_spec0 RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (bv_unsigned sp - 2136) 354544 (bv_unsigned sp) (al_ctx L) t top bot lo (words_of_bytes junk1)).
        all: try lazymatch goal with
             | |- stk _ _ _ _ => rewrite Hsp; exact STa
             | |- mem_inv _ _ => exact MIa
             | |- @eq word _ _ => first [reflexivity | exact TP | rewrite Z_to_bv_bv_unsigned; reflexivity | apply Z_to_bv_eqm; rewrite ?unsigned_lit by lia; lia]
             | |- ex _ => first [eexists; exact SZC | eexists; exact BPJ]
             | |- u64arr _ _ _ _ => exact TB
             | |- uchain _ _ _ _ _ _ _ => exact UC1
             | |- _ \/ _ => unboxed CT2
             | |- rng _ _ _ => solve_rng
             | |- rw_cells _ _ (_ + 152) _ => exact CT
             | |- rw_cells _ _ (_ + 8) [C8 _; C8 _] => exact TT
             | |- rw_cells _ _ (_ + 40) _ => exact SW
             | |- rw_cells _ _ (_ + 3168) _ => exact UW
             end.
        all: try eassumption. all: try (unfold AIMG_HI; lia). all: try (Z.div_mod_to_equations; lia).
        all: match goal with |- ?G => idtac "REMU" G end. }

  cbv beta. intros ms2 PU. unfold unwind_impl_post in PU.
  (nd_pre PU 18%nat; intros t0b t1b t2b a0b a1b a2b a3b a4b a5b a6b a7b t3b t4b t5b t6b m2 tb2 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 10%nat; intros MUu WMu MIu STu SZ2 TB2 LTB2 TRF2 BP2 UW2; nd_post).
  unname_sp. rewrite ?unsigned_lit in MUu by lia. rewrite ?unsigned_lit in STu by lia.
  replace (ret_pc (Z_to_bv 64 354636)) with (Z_to_bv 64 354636) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  (* [comment removed for export] *)
  xport STATS MUu WMu ltac:(rewrite LSJ; lia).
  xport TI MUu WMu ltac:(lia). xport TK MUu WMu ltac:(lia). xport T88 MUu WMu ltac:(lia). xport TSD MUu WMu ltac:(lia).
  xport CT MUu WMu ltac:(ub CT2; lia).
  eapply evtF_mono.
  { eapply (ricptB_spec RNG) with (p := p) (n := n) (ctx := al_ctx L) (t := t) (sj := sj);
      [exact STu | atop_facts; lia | lia | exact MIu | exact TP | reflexivity | reflexivity | lia | exact NR
      | exact TI | exact TK | exact T88 | exact TSD | exact CT | lia | unfold AIMG_HI; lia | exact CX1 | exact T0i | exact T1 | unboxed CT2
      | exact STATS | exact LSJ | exact RIMG | exact RTLS | solve_rng | exact RCTX | exact RT]. }
  cbv beta. intros ms3 PB. unfold ricptB_post in PB. (nd_pre PB 4%nat; intros m3 fr0 sj3 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 8%nat; intros MUb WMb MIb STb FR48 FR16 STATS3 LSJ3; nd_post).
  (* [comment removed for export] *)
  assert (MU3 : munch (realloc_pre_W sp t) m m3).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUb]]. eapply munch_trans; [| eapply munch_weaken; [| exact MUu]].
    eapply munch_weaken; [| exact MUa]. all: unfold sub_fp; cbn [outside]; intros q Hq; lia. }
  assert (WM3 : wmono asegs m m3). { eapply wmono_trans; [| exact WMb]. eapply wmono_trans; [exact WMa | exact WMu]. }
  assert (MU13 : munch [(bv_unsigned sp - 2368, bv_unsigned sp - 2144); (bv_unsigned sp - 2128, bv_unsigned sp - 2124); (bv_unsigned sp - 2120, bv_unsigned sp - 72); (t + 3168, t + 3169); (t + 2800, t + 2800 + 368)]%Z m1 m3).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUb]]. eapply munch_weaken; [| exact MUu].
    all: unfold sub_fp; cbn [outside]; intros q Hq; lia. }
  assert (WM13 : wmono asegs m1 m3). { eapply wmono_trans; [exact WMu | exact WMb]. }
  xport FRp MU13 WM13 ltac:(lia). xport TAG MU13 WM13 ltac:(lia). xport FRP MU13 WM13 ltac:(lia). xport REST MU13 WM13 ltac:(lia).
  xport FL1 MU13 WM13 ltac:(lia). xport IAS1 MU13 WM13 ltac:(lia).
  assert (IAM3 : forall j, 0 <= j < 32768 -> bytes_at asegs m3 (0xaf808 + 8 * j) (le8 (Z_to_bv 64 0))).
  { intros j Hj. eapply bytes_at_agree; [exact (IAM1 j Hj)|].
    intros i Hi. apply MU13. cbn [outside]. rewrite length_le8 in Hi. rewrite wa_unsigned by lia. lia. }
  (* [comment removed for export] *)
  xport SZ2 MUb WMb ltac:(lia). replace (bv_unsigned sp - 2136 + 8) with (bv_unsigned sp + -2128) in SZ2 by lia.
  rw_join SZ2 TAG SZT. rw_join FRp SZT SS.
  xport TB2 MUb WMb ltac:(rewrite LTB2; lia). xport BP2 MUb WMb ltac:(lia). xport UW2 MUb WMb ltac:(lia).
  rewrite Z_to_bv_bv_unsigned in BP2. rw_join BP2 REST FRS.
  replace (bv_unsigned sp - 2136 + 2056) with (bv_unsigned sp + -80) in FRS by lia.
  unfold realloc_pre_post. do 13 eexists. exists m3.
  split; [reflexivity|]. split; [exact MU3|]. split; [exact WM3|]. split; [exact MIb|]. split; [exact STb|].
  split; [exact FR48|]. split; [exact FR16|]. split; [exact FRP|].
  split; [replace (bv_unsigned sp + -2136 + 16) with (bv_unsigned sp + -2120) by lia; exact SS|].
  split; [replace (bv_unsigned sp + -2136 + 16) with (bv_unsigned sp - 2136 + 16) by lia; exact TB2|]. split; [exact LTB2|].
  split; [exact TRF2|]. split; [exact FRS|]. split; [exact UW2|]. split; [exact STATS3|]. split; [exact LSJ3|].
  split; [exact FL1|]. split; [exact IAS1|]. exact IAM3.
Qed.
End Zd1.
#[using="Type"] Lemma realloc_pre_spec : ltac:(let t := eval cbv delta [realloc_pre_spec__stmt] in realloc_pre_spec__stmt in exact t).
Proof. exact realloc_pre_spec__body. Qed.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc1b__A3W.F_aalloc1b.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aunwind.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc1b__A3W.F_aunwind2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc__A3W.F_amalloc_icpt.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3g0__A3W.F_arealloc_iseg.TwB.
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



(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Notation realloc_pre_W sp t :=
  ([(bv_unsigned sp - 2368, bv_unsigned sp); (0xafc00, 0xafc00 + 0x81030); (0x13e488, 0x13e488 + 4); (t + 3168, t + 3169);
    (t + 2800, t + 2800 + 368)]%Z) (only parsing).

Definition realloc_pre_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (p n t lo : Z) (trc : list Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a7 t3 t4 t5 t6 (fr0 junk0 junk2 : list byte) (tb sj' : list word) m',
    ms' = MS (mkR (Z_to_bv 64 0x347f0) (Z_to_bv 64 (bv_unsigned sp + -2208)) gp tp t0 t1 t2
                  (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 p)
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 n) (Z_to_bv 64 8) (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 1) (Z_to_bv 64 1)
                  (Z_to_bv 64 (bv_unsigned sp + -2136)) a7
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 n) (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 (bv_unsigned sp + -89))
                  s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x33c70) fc None m' (seg_rom asegs)
    /\ munch (realloc_pre_W sp t) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -2208)
    /\ rw_cells asegs m' (bv_unsigned sp + -2208) [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 0x56958); C8 (Z_to_bv 64 p); C8 (Z_to_bv 64 n); C8 sp; C8 (Z_to_bv 64 0x34774)]
    /\ rw_cells asegs m' (bv_unsigned sp + -2160) [CB 8 fr0; C8 (Z_to_bv 64 0x569c8)]
    /\ rw_cells asegs m' (bv_unsigned sp + -2144) [CB 8 junk0]
    /\ rw_cells asegs m' (bv_unsigned sp + -2136) [C8 (Z_to_bv 64 (bv_unsigned sp + -2136 + 16)); C4 (Z_to_bv 64 (1 + Z.of_nat (length trc))); C4 (Z_to_bv 64 0)]
    /\ u64arr asegs m' (bv_unsigned sp + -2136 + 16) tb /\ length tb = 255%nat
    /\ map bv_unsigned (firstn (Datatypes.S (length trc)) tb) = AREALLOC_PC' :: trc
    /\ rw_cells asegs m' (bv_unsigned sp + -80) [C8 sp; CB 8 junk2; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' (t + 3168) [C1 (Z_to_bv 8 0)]
    /\ u64arr asegs m' (t + 2800) sj' /\ length sj' = 46%nat
    /\ rw_cells asegs m' 0x13e488 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ stk asegs m' 0xafc00 (0xafc00 + 0x81030)
    /\ (forall j, 0 <= j < 32768 -> bytes_at asegs m' (0xafc08 + 8 * j) (le8 (Z_to_bv 64 0))).

Definition realloc_pre_spec__stmt : Prop := forall (L : alayout) (ia : bool) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (p n t lo top bot : Z) (tr trc : list Z) (sj : list word),
  let ctx := al_ctx L in
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 n -> 1 <= p < 2^47 -> 1 <= n < 2^64 ->
  bv_unsigned sp mod 16 = 0 ->
  (* [comment removed for export] *)
  allocA_cells m ctx t ->
  rw_cells asegs m 0xa5880 [C8 (Z_to_bv 64 0x140528); C8 (Z_to_bv 64 0xac1f8); C8 (Z_to_bv 64 0xae9f8);
                             C8 (Z_to_bv 64 0xaf6e8); C8 (Z_to_bv 64 0xaf6f0); C8 (Z_to_bv 64 0xaf6e0)] ->
  rw_cells asegs m 0xaf6fc [C4 (Z_to_bv 64 30)] ->
  rw_cells asegs m 0x14054a [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m GOT_PGSZ [C8 (Z_to_bv 64 APGSZ)] -> rw_cells asegs m APGSZ [C8 (Z_to_bv 64 4096)] ->
  rw_cells asegs m 0xa5870 [C8 (Z_to_bv 64 0x13e4a0)] -> rw_cells asegs m 0x13e4a0 [C8 (Z_to_bv 64 4096)] ->
  (* [comment removed for export] *)
  rw_cells asegs m AIA_FLAG [C1 (Z_to_bv 8 (if ia then 1 else 0)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  stk asegs m AIA_BASE (AIA_BASE + AIA_SIZE) ->
  (ia = true -> forall j, 0 <= j < 32768 -> bytes_at asegs m (AIA_MAP1 + 8 * j) (le8 (Z_to_bv 64 0))) ->
  (* [comment removed for export] *)
  rw_cells asegs m (ctx + 8) [C4 (Z_to_bv 64 0)] -> rw_cells asegs m t [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (t + 8) [C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)] ->
  rw_cells asegs m (t + 40) [C1 (Z_to_bv 8 0)] -> rw_cells asegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> sclr ctx 65536 ->
  iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> t mod 4096 = 0 -> sclr t 4096 ->
  (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  (* [comment removed for export] *)
  (bv_unsigned sp + 16 < top /\ uchain m top AREALLOC_PC' (bv_unsigned sp) (bv_unsigned s0) 28%nat tr /\ (length tr <= 28)%nat /\ trc = bv_unsigned ra :: tr
   /\ rng RNG lo (top - lo))
  \/ (top <= bv_unsigned sp + 16 /\ bv_unsigned sp < 2^47 /\ trc = []) ->
  bv_unsigned s0 <> bv_unsigned sp + 8 ->
  0 <= bot -> bot < bv_unsigned sp -> bot + 4096 <= top -> top <= 2^47 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AREALLOC_PC' ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  evtF asegs RNG (realloc_pre_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc p n t lo trc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AREALLOC_SYM') fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 0).
Variable ia : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 1).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 2).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 3).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 4).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 5).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 6).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 7).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 8).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 9).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 10).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 11).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 12).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 13).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 14).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 15).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 16).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 17).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 18).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 19).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 20).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 21).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 22).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 23).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 24).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 25).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 26).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 27).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 28).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 29).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 30).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 31).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 32).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 33).
Variable F : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 34).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 35).
Variable m : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 36).
Variable p : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 37).
Variable n : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 38).
Variable t : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 39).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 40).
Variable top : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 41).
Variable bot : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 42).
Variable tr : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 43).
Variable trc : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 44).
Variable sj : ltac2:(SecDietF.SzSecF.ty 'realloc_pre_spec__stmt 45).
#[using="Type"] Lemma realloc_pre_spec__body : ltac:(let T := type of (fun (h : realloc_pre_spec__stmt) => h L ia RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p n t lo top bot tr trc sj) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (ia, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (p, (n, (t, (lo, (top, (bot, (tr, (trc, sj)))))))))))))))))))))))))))))))))))))))))))))) as _.
 cbv zeta.
  intros ST CEIL LO MI TP Ha0 Ha1 PR NR SP16 AC GOT LS1 CT8 GPG PGC PG1 PG2 FL IAS IAM CX8 TT0 TT SW UW STATS LSJ CX0 CX1 CXS T0 T1 TAL TS CT2
         ARM S0NE B0 BB BTOP TOP RA4 RANE RIMG RTLS RSTK RCTX RT.
  pose proof T0 as T0i. band_lin.   (* [comment removed for export] *)
  assert (LTRC : (length trc <= 29)%nat) by (destruct ARM as [(_ & _ & L1 & -> & _)|(_ & _ & ->)]; cbn [length]; lia).
  assert (SP47 : bv_unsigned sp < 2^47) by (destruct ARM as [(X1 & _)|(_ & X2 & _)]; lia).
  pose proof AC as AC'. (nd_pre AC' 8%nat; intros INI RSS IMAX TI TK T88 TSD CT; nd_post).
  unfold AIMG_HI, AINSTANCE, ATP88, ATSD, ATSDI, ATSDK, AINITED, ARSSLIM, GOT_PGSZ, APGSZ, AREALLOC_PC', AIA_FLAG, AIA_BASE, AIA_SIZE, AIA_MAP1 in *.
  word_range sp SPR. word_range s0 S0R. word_range ra RAR.
  box CT2.
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (ricptA_spec ia RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p n lo);
      try eassumption; try lia; try solve_rng. }
  cbv beta. intros ms1 PA. unfold ricptA_post in PA.
  (nd_pre PA 14%nat; intros t0a t1a t2a a6a a7a t3a t4a t5a t6a m1 junk0 junk1 junk2 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 11%nat; intros MUa WMa MIa STa FRP FRA FRt FRs FL1 IAS1 IAM1; nd_post).
  (* [comment removed for export] *)
  pose proof FRs as FRs0. rw_split FRs0 8%nat FRsx FRsr. clear FRsx.
  destruct FRsr as [[_ BSR] _]. cbn [cells_bytes cbytes app] in BSR. rewrite app_nil_r in BSR.
  apply bytes_at_app in BSR. destruct BSR as [BS0 BRA]. rewrite length_le8 in BRA.
  replace (bv_unsigned sp + -16 + Z.of_nat 8) with (bv_unsigned sp - 8) in BRA by lia.
  replace (bv_unsigned sp + -16) with (bv_unsigned sp - 16) in BS0 by lia.
  (* [comment removed for export] *)
  xport TI MUa WMa ltac:(lia). xport TK MUa WMa ltac:(lia). xport T88 MUa WMa ltac:(lia). xport TSD MUa WMa ltac:(lia).
  xport CT MUa WMa ltac:(lia). xport GPG MUa WMa ltac:(lia). xport PGC MUa WMa ltac:(lia). xport TT MUa WMa ltac:(lia).
  xport SW MUa WMa ltac:(lia). xport UW MUa WMa ltac:(lia). xport INI MUa WMa ltac:(lia).
  xport STATS MUa WMa ltac:(rewrite LSJ; lia).
  pose proof FRA as FRA0. rw_split FRA0 1%nat FRp FRz. rw_split FRz 1%nat SZC TAG.
  change 2040%nat with (8 * 255)%nat in FRt. destruct (u64arr_of_CB _ _ 255%nat _ FRt) as [TB LTB].
  pose proof FRs as FRs1. rw_split FRs1 1%nat BPJ REST.
  replace (bv_unsigned sp + -2128) with (bv_unsigned sp - 2136 + 8) in SZC by lia.
  replace (bv_unsigned sp + -2120) with (bv_unsigned sp - 2136 + 16) in TB by lia.
  replace (bv_unsigned sp + -80) with (bv_unsigned sp - 2136 + 2056) in BPJ by lia.
  (* [comment removed for export] *)
  step.                                                          (* [comment removed for export] *)
  name_sp sp (-2144).
  eapply evtF_cut with (P := unwind_impl_post (bv_unsigned sp - 2136) 354648 (bv_unsigned sp) t _ _ gp tp _ _ _ _ _ _ _ s7 s8 s9 s10 s11 F fc lo trc m1).
  { destruct ARM as [(BT & UC & LTR & Etrc & RTOP)|(BT & BT2 & Etrc)]; rewrite Etrc.
    - (* [comment removed for export] *)
      assert (UC1 : uchain m1 top 354648 bot (bv_unsigned sp) 29%nat ([bv_unsigned ra] ++ tr)).
      { replace ([bv_unsigned ra] ++ tr) with ((if bv_unsigned ra =? 354648 then [] else [bv_unsigned ra]) ++ tr)
          by (replace (bv_unsigned ra =? 354648) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
        eapply (uc_step m1 top 354648 bot (bv_unsigned sp) 29%nat (bv_unsigned s0) (bv_unsigned ra) tr); try lia.
        - rewrite Z_to_bv_bv_unsigned. exact BS0.
        - rewrite Z_to_bv_bv_unsigned. exact BRA.
        - replace (bv_unsigned ra =? 354648) with false by (symmetry; apply Z.eqb_neq; lia). cbn [Nat.pred].
          destruct (Z_le_gt_dec (bv_unsigned sp + 16) (bv_unsigned s0)) as [GE|LT].
          + eapply uchain_frame; [exact UC|]. intros a Ha. apply MUa. cbn [outside]. rewrite unsigned_lit by lia. pose proof atop_range as ATR9. split; [lia|]. split; [lia|]. split; [lia| exact I].
          + inversion UC; subst; [apply uc_stop; assumption | exfalso | exfalso]; Z.div_mod_to_equations; lia. }
      clear BS0 BRA UC.
      change (bv_unsigned ra :: tr) with ([bv_unsigned ra] ++ tr).
    eapply (unwind_impl_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (bv_unsigned sp - 2136) 354648 (bv_unsigned sp) (al_ctx L) t top bot lo (words_of_bytes junk1) ([bv_unsigned ra] ++ tr)).
        all: try lazymatch goal with
             | |- stk _ _ _ _ => rewrite Hsp; exact STa
             | |- mem_inv _ _ => exact MIa
             | |- @eq word _ _ => first [reflexivity | exact TP | rewrite Z_to_bv_bv_unsigned; reflexivity | apply Z_to_bv_eqm; rewrite ?unsigned_lit by lia; lia]
             | |- ex _ => first [eexists; exact SZC | eexists; exact BPJ]
             | |- u64arr _ _ _ _ => exact TB
             | |- uchain _ _ _ _ _ _ _ => exact UC1
             | |- _ \/ _ => unboxed CT2
             | |- rng _ _ _ => solve_rng
             | |- rw_cells _ _ (_ + 152) _ => exact CT
             | |- rw_cells _ _ (_ + 8) [C8 _; C8 _] => exact TT
             | |- rw_cells _ _ (_ + 40) _ => exact SW
             | |- rw_cells _ _ (_ + 3168) _ => exact UW
             end.
        all: try eassumption. all: try (unfold AIMG_HI; lia). all: try (Z.div_mod_to_equations; lia).
        all: match goal with |- ?G => idtac "REMU" G end.
    - (* [comment removed for export] *)
      clear BS0 BRA.
    eapply (unwind_impl_spec0 RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (bv_unsigned sp - 2136) 354648 (bv_unsigned sp) (al_ctx L) t top bot lo (words_of_bytes junk1)).
        all: try lazymatch goal with
             | |- stk _ _ _ _ => rewrite Hsp; exact STa
             | |- mem_inv _ _ => exact MIa
             | |- @eq word _ _ => first [reflexivity | exact TP | rewrite Z_to_bv_bv_unsigned; reflexivity | apply Z_to_bv_eqm; rewrite ?unsigned_lit by lia; lia]
             | |- ex _ => first [eexists; exact SZC | eexists; exact BPJ]
             | |- u64arr _ _ _ _ => exact TB
             | |- uchain _ _ _ _ _ _ _ => exact UC1
             | |- _ \/ _ => unboxed CT2
             | |- rng _ _ _ => solve_rng
             | |- rw_cells _ _ (_ + 152) _ => exact CT
             | |- rw_cells _ _ (_ + 8) [C8 _; C8 _] => exact TT
             | |- rw_cells _ _ (_ + 40) _ => exact SW
             | |- rw_cells _ _ (_ + 3168) _ => exact UW
             end.
        all: try eassumption. all: try (unfold AIMG_HI; lia). all: try (Z.div_mod_to_equations; lia).
        all: match goal with |- ?G => idtac "REMU" G end. }

  cbv beta. intros ms2 PU. unfold unwind_impl_post in PU.
  (nd_pre PU 18%nat; intros t0b t1b t2b a0b a1b a2b a3b a4b a5b a6b a7b t3b t4b t5b t6b m2 tb2 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 10%nat; intros MUu WMu MIu STu SZ2 TB2 LTB2 TRF2 BP2 UW2; nd_post).
  unname_sp. rewrite ?unsigned_lit in MUu by lia. rewrite ?unsigned_lit in STu by lia.
  replace (ret_pc (Z_to_bv 64 354740)) with (Z_to_bv 64 354740) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  (* [comment removed for export] *)
  xport STATS MUu WMu ltac:(rewrite LSJ; lia).
  xport TI MUu WMu ltac:(lia). xport TK MUu WMu ltac:(lia). xport T88 MUu WMu ltac:(lia). xport TSD MUu WMu ltac:(lia).
  xport CT MUu WMu ltac:(ub CT2; lia).
  eapply evtF_mono.
  { eapply (ricptB_spec RNG) with (p := p) (n := n) (ctx := al_ctx L) (t := t) (sj := sj);
      [exact STu | atop_facts; lia | lia | exact MIu | exact TP | reflexivity | reflexivity | lia | exact NR
      | exact TI | exact TK | exact T88 | exact TSD | exact CT | lia | unfold AIMG_HI; lia | exact CX1 | exact T0i | exact T1 | unboxed CT2
      | exact STATS | exact LSJ | exact RIMG | exact RTLS | solve_rng | exact RCTX | exact RT]. }
  cbv beta. intros ms3 PB. unfold ricptB_post in PB. (nd_pre PB 4%nat; intros m3 fr0 sj3 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 8%nat; intros MUb WMb MIb STb FR48 FR16 STATS3 LSJ3; nd_post).
  (* [comment removed for export] *)
  assert (MU3 : munch (realloc_pre_W sp t) m m3).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUb]]. eapply munch_trans; [| eapply munch_weaken; [| exact MUu]].
    eapply munch_weaken; [| exact MUa]. all: unfold sub_fp; cbn [outside]; intros q Hq; lia. }
  assert (WM3 : wmono asegs m m3). { eapply wmono_trans; [| exact WMb]. eapply wmono_trans; [exact WMa | exact WMu]. }
  assert (MU13 : munch [(bv_unsigned sp - 2368, bv_unsigned sp - 2144); (bv_unsigned sp - 2128, bv_unsigned sp - 2124); (bv_unsigned sp - 2120, bv_unsigned sp - 72); (t + 3168, t + 3169); (t + 2800, t + 2800 + 368)]%Z m1 m3).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUb]]. eapply munch_weaken; [| exact MUu].
    all: unfold sub_fp; cbn [outside]; intros q Hq; lia. }
  assert (WM13 : wmono asegs m1 m3). { eapply wmono_trans; [exact WMu | exact WMb]. }
  xport FRp MU13 WM13 ltac:(lia). xport TAG MU13 WM13 ltac:(lia). xport FRP MU13 WM13 ltac:(lia). xport REST MU13 WM13 ltac:(lia).
  xport FL1 MU13 WM13 ltac:(lia). xport IAS1 MU13 WM13 ltac:(lia).
  assert (IAM3 : forall j, 0 <= j < 32768 -> bytes_at asegs m3 (0xafc08 + 8 * j) (le8 (Z_to_bv 64 0))).
  { intros j Hj. eapply bytes_at_agree; [exact (IAM1 j Hj)|].
    intros i Hi. apply MU13. cbn [outside]. rewrite length_le8 in Hi. rewrite wa_unsigned by lia. lia. }
  (* [comment removed for export] *)
  xport SZ2 MUb WMb ltac:(lia). replace (bv_unsigned sp - 2136 + 8) with (bv_unsigned sp + -2128) in SZ2 by lia.
  rw_join SZ2 TAG SZT. rw_join FRp SZT SS.
  xport TB2 MUb WMb ltac:(rewrite LTB2; lia). xport BP2 MUb WMb ltac:(lia). xport UW2 MUb WMb ltac:(lia).
  rewrite Z_to_bv_bv_unsigned in BP2. rw_join BP2 REST FRS.
  replace (bv_unsigned sp - 2136 + 2056) with (bv_unsigned sp + -80) in FRS by lia.
  unfold realloc_pre_post. do 13 eexists. exists m3.
  split; [reflexivity|]. split; [exact MU3|]. split; [exact WM3|]. split; [exact MIb|]. split; [exact STb|].
  split; [exact FR48|]. split; [exact FR16|]. split; [exact FRP|].
  split; [replace (bv_unsigned sp + -2136 + 16) with (bv_unsigned sp + -2120) by lia; exact SS|].
  split; [replace (bv_unsigned sp + -2136 + 16) with (bv_unsigned sp - 2136 + 16) by lia; exact TB2|]. split; [exact LTB2|].
  split; [exact TRF2|]. split; [exact FRS|]. split; [exact UW2|]. split; [exact STATS3|]. split; [exact LSJ3|].
  split; [exact FL1|]. split; [exact IAS1|]. exact IAM3.
Qed.
End Zd1.
#[using="Type"] Lemma realloc_pre_spec : ltac:(let t := eval cbv delta [realloc_pre_spec__stmt] in realloc_pre_spec__stmt in exact t).
Proof. exact realloc_pre_spec__body. Qed.
End CANSEC1.
End TwB.
End F_arealloc_pre.
