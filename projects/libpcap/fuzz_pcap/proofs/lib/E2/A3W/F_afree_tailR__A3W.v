(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase AQConst.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_adrain__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_tail.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require NDestr.
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AProto.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecSlog__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_front__A3W.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_afree_tailR.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase AQConst. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_adrain__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_tail. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_aenqueue OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_aenqueueR OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_adrain OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_aput OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tail.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac ag_arith := lazymatch goal with
  | |- Z.le _ _ => idtac | |- Z.lt _ _ => idtac | |- Z.ge _ _ => idtac | |- Z.gt _ _ => idtac
  | |- le _ _ => idtac | |- lt _ _ => idtac | |- ge _ _ => idtac | |- gt _ _ => idtac
  | |- @eq _ _ _ => idtac | |- not _ => idtac | |- and _ _ => idtac | |- or _ _ => idtac | |- False => idtac | |- True => idtac
  end.
(* [comment removed for export] *)
Local Ltac nz_box H HZ := lazymatch type of H with @length ?A ?l = ?n =>
  let z := eval vm_compute in (Z.of_nat n) in assert (HZ : Z.of_nat (@length A l) = z) by (rewrite H; reflexivity); box H end.
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
Local Ltac fp_cover8 := apply sub_fp_cover8; repeat (apply Forall_cons; [ cbn [fst snd]; first [left; fp_cheap8 | right; fp_find8c | right; fp_find8] | ]); apply Forall_nil.
(* [comment removed for export] *)
Local Ltac transport_call_munch_tac ::= first [ fp_cover8 | unfold sub_fp; cbn [outside]; first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs; intros; lia end | clear; intros; lia | intros; slia ] ].
(* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.
(* [comment removed for export] *)
Local Ltac with_sclr tac := idtac; match goal with H : sclr ?a ?n |- _ => with_band H tac | _ => tac end.  (* [comment removed for export] *)

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
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition put_to_refill_post (full : bool) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 : word) (F : bvmap 5 word) (fc : bv 32)
    (t hm n lo lst nx bsz : Z) (hs : list word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) m' (j0 : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x382f8) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2
                  (Z_to_bv 64 (t + 2128)) (Z_to_bv 64 (t + 208))
                  (Z_to_bv 64 (t + 208)) (Z_to_bv 64 (t + 2128)) (Z_to_bv 64 0xaaf98) (Z_to_bv 64 K_BATCH_CLASS) a4 a5 a6 a7
                  (Z_to_bv 64 hm) (Z_to_bv 64 (t + 80)) a3 (Z_to_bv 64 n) (Z_to_bv 64 Q_CACHE) s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x38ad8) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 144, bv_unsigned sp); (shad (hm + 16), shad (hm + 16) + shlen (rup n 8))]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -144)
    /\ rw_cells asegs m' (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) (repeat (Z_to_bv 8 253) (Z.to_nat (shlen (rup n 8))))]
    /\ rw_cells asegs m' (bv_unsigned sp + -80) [C8 a2; C8 a3; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' (bv_unsigned sp + -144)
         [CB 8 j0; C8 (Z_to_bv 64 hm); C8 a2; C8 a3; C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 (t + 80)); C8 (Z_to_bv 64 0xab270); C8 (Z_to_bv 64 0x38198)]
    /\ (if full then rw_cells asegs m' lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)] /\ u64arr asegs m' (lst + 24) hs else True).

Definition put_to_refill_spec__stmt : Prop := forall (full : bool) (t hm lst : Z) RNG
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n nb fst0 qb b1 actx lo nx bsz : Z) (maxc csz : word) (hs : list word) (sjunk : list byte),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 144 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 0xab270 -> a1 = Z_to_bv 64 (t + 80) -> a2 = Z_to_bv 64 (t + 208) -> a4 = Z_to_bv 64 hm -> a5 = Z_to_bv 64 n ->
  (* [comment removed for export] *)
  rw_cells asegs m 0xab2b0 [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->
  rw_cells asegs m 0xa54a8 [C8 (Z_to_bv 64 AFLAGS)] ->
  rw_cells asegs m 0xabe24 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->
  poison_cells m ->
  (* [comment removed for export] *)
  rw_cells asegs m hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  1 <= n <= Q_MAX -> 0 <= b1 < 256 -> hm mod 16 = 0 -> ablk hm (hm + 16 + rup n 8) -> tclr hm 24 -> hm + 16 + rup n 8 <= ATOP -> hm + 16 <= ATOP ->
  rw_cells asegs m (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) sjunk] ->
  (* [comment removed for export] *)
  rw_cells asegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= lst < 2^64 ->
  sclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> t mod 4096 = 0 -> (hm + 16 <= t \/ t + 4096 <= hm) ->
  (* [comment removed for export] *)
  (if full then 0 < nb /\ rw_cells asegs m lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)]
             /\ 0x10007fff8000 <= lst /\ lst + 8192 <= ATOP
             /\ u64arr asegs m (lst + 24) hs /\ length hs = 1021%nat /\ rng RNG lst 8192
   else nb = 0 /\ lst = 0) ->
  rw_cells asegs m (t + 2128) [C4 (Z_to_bv 64 0); C4 maxc; C8 csz] ->
  (t + 4096 <= lst \/ lst + 8192 <= t \/ lst = 0) -> (hm + 16 <= lst \/ lst + 8192 <= hm) ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 -> rng RNG hm 16 -> rng RNG (shad (hm + 16)) (shlen (rup n 8)) ->
  iclr t 4096 ->                                            (* [comment removed for export] *)
  evtF asegs RNG (put_to_refill_post full ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 F fc t hm n lo lst nx bsz hs m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x37ff4) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable full : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 0).
Variable t : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 1).
Variable hm : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 2).
Variable lst : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 3).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 4).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 5).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 6).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 7).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 8).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 9).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 10).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 11).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 12).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 13).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 14).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 15).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 16).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 17).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 18).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 19).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 20).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 21).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 22).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 23).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 24).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 25).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 26).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 27).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 28).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 29).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 30).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 31).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 32).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 33).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 34).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 35).
Variable F : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 36).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 37).
Variable m : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 38).
Variable n : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 39).
Variable nb : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 40).
Variable fst0 : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 41).
Variable qb : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 42).
Variable b1 : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 43).
Variable actx : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 44).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 45).
Variable nx : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 46).
Variable bsz : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 47).
Variable maxc : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 48).
Variable csz : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 49).
Variable hs : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 50).
Variable sjunk : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 51).
#[using="Type"] Lemma put_to_refill_spec__body : ltac:(let T := type of (fun (h : put_to_refill_spec__stmt) => h full t hm lst RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n nb fst0 qb b1 actx lo nx bsz maxc csz hs sjunk) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (full, (t, (hm, (lst, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (n, (nb, (fst0, (qb, (b1, (actx, (lo, (nx, (bsz, (maxc, (csz, (hs, sjunk)))))))))))))))))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO MI -> -> -> -> -> QK GF FLG PC HD N B1 AL HLO TCH HHI HCE SH QC NB LST T0 T1 TAL DHT FULL CR DTL DHL RIMG RTLS RSTK RT RH RSH TI.
  band_int TI. (pose proof (ablk_lin _ _ HLO) as ndP__; nd_pre ndP__ 4%nat; intros HL1 HL2 HL3 HL4; nd_post). unfold AIMG_HI in HL1. band_int HLO. band_lin. band_int T0.   (* [comment removed for export] *)
  assert (SHB : 2148238848 <= shad (hm + 16) /\ shad (hm + 16) + shlen (rup n 8) <= 0x10007fff8000).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold Q_MAX in N. Z.div_mod_to_equations. lia. }
  assert (RUP : n <= rup n 8 <= n + 7 /\ rup n 8 mod 8 = 0) by (clear; unfold rup; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
  assert (SHL : 0 < shlen (rup n 8) < 0x10000000) by (unfold shlen; rewrite Z.shiftr_div_pow2 by lia; unfold Q_MAX in N; Z.div_mod_to_equations; lia).
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (shad (hm + 16), shad (hm + 16) + shlen (rup n 8))]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  (nd_pre PC 7%nat; intros P1 P2 P3 P4 P5 P6 P7; nd_post).
  box DHT. box DTL. box DHL.
  destruct full; [(nd_pre FULL 7%nat; intros NB1 LB L0 L1 LA0 LEN0 RL; nd_post); nz_box LEN0 LEN0Z | destruct FULL as [NB0 LST0]];
  unfold AIMG_HI in *.
  - (* [comment removed for export] *)
    box ST.   (* [comment removed for export] *)
    call (putA_spec t hm n); try unboxed ST; try eassumption; try reflexivity; try (ag_arith; unfold Q_MAX, AIMG_HI in *; lia).
    try clear ST.
    rename POST into FRP.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end. try rename MI0 into MI.
    box SH.   (* [comment removed for export] *)
    box ST.
    step. call_sp (poison_shadow_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (hm + 16) (rup n 8) 253 lo sjunk);
      [unboxed ST| exact CEIL| lia| exact MI| repeat (split; [assumption|]); assumption| reflexivity| reflexivity| reflexivity
      | Z.div_mod_to_equations; lia| lia| lia| first [assumption | (eapply ablk_sub; [exact HLO| clear; lia| clear; lia]) | unfold ablk; right; lia | unfold ablk; left; lia]| lia| lia| lia| unboxed SH|].
    try clear ST.
    clear SH.   (* [comment removed for export] *)
    try rename MI0 into MI. clear P1 P2 P3 P4 P5 P6 P7.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    match goal with H : rw_cells asegs ?mm (shad (hm + 16)) _ |- _ => rename H into SH' end.
    do 5 step.                                 (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    box HD. box SH'. box LA0. box LB. box FRP.
    snapshot [(bv_unsigned sp + -80 - 64, bv_unsigned sp + -80)]%Z MUe WMe.
    box ST.
    call_sp (enqueue_to_refill_spec true t lst RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz lo maxc csz);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| reflexivity| reflexivity| exact QC| lia| lia
      | split; [lia|]; split; [ub LB; exact Y|]; split; [unfold AIMG_HI; lia|]; split; [unfold Q_BATCH_BYTES; lia| exact RL]
      | exact CR| exact TI| atop_facts; lia| exact TAL| ub DTL; unfold Q_BATCH_BYTES; lia|].
    try clear ST.
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(lia). carry SH' MUe WMe ltac:(lia). carry LA0 MUe WMe ltac:(rewrite LEN0Z; lia). carry LB MUe WMe ltac:(lia). carry FRP MUe WMe ltac:(lia). clear MUe WMe.
    replace (bv_unsigned sp + -80 + -64) with (bv_unsigned sp + -144) in * by lia.
    unfold put_to_refill_post. finish.
    all: try assumption. all: try eassumption. all: try exact I. all: try (split; assumption).
  - (* [comment removed for export] *)
    box ST.   (* [comment removed for export] *)
    call (putA_spec t hm n); try unboxed ST; try eassumption; try reflexivity; try (ag_arith; unfold Q_MAX, AIMG_HI in *; lia).
    try clear ST.
    rename POST into FRP.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end. try rename MI0 into MI.
    box SH.   (* [comment removed for export] *)
    box ST.
    step. call_sp (poison_shadow_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (hm + 16) (rup n 8) 253 lo sjunk);
      [unboxed ST| exact CEIL| lia| exact MI| repeat (split; [assumption|]); assumption| reflexivity| reflexivity| reflexivity
      | Z.div_mod_to_equations; lia| lia| lia| first [assumption | (eapply ablk_sub; [exact HLO| clear; lia| clear; lia]) | unfold ablk; right; lia | unfold ablk; left; lia]| lia| lia| lia| unboxed SH|].
    try clear ST.
    clear SH.   (* [comment removed for export] *)
    try rename MI0 into MI. clear P1 P2 P3 P4 P5 P6 P7.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    match goal with H : rw_cells asegs ?mm (shad (hm + 16)) _ |- _ => rename H into SH' end.
    do 5 step.
    step.
    box HD. box SH'. box FRP.
    snapshot [(bv_unsigned sp + -80 - 64, bv_unsigned sp + -80)]%Z MUe WMe.
    box ST.
    call_sp (enqueue_to_refill_spec false t lst RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz lo maxc csz);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| reflexivity| reflexivity| exact QC| lia| lia
      | exact NB0
      | exact CR| exact TI| atop_facts; lia| exact TAL| ub DTL; unfold Q_BATCH_BYTES; lia|].
    try clear ST.
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(lia). carry SH' MUe WMe ltac:(lia). carry FRP MUe WMe ltac:(lia). clear MUe WMe.
    replace (bv_unsigned sp + -80 + -64) with (bv_unsigned sp + -144) in * by lia.
    unfold put_to_refill_post. finish.
    all: try assumption. all: try eassumption. all: try exact I.
Qed.
End Zd1.
#[using="Type"] Lemma put_to_refill_spec : ltac:(let t := eval cbv delta [put_to_refill_spec__stmt] in put_to_refill_spec__stmt in exact t).
Proof. exact put_to_refill_spec__body. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition put_from_refill_spec__stmt : Prop := forall (full : bool) (g : gqd) (t hm lst b : Z) RNG
    (ra sp gp tp s0 s1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (ra0 t0 t1 t2 a1 a2' a3' a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : amem) (n nb fst0 qb b1 actx lo nx bsz cnt spacebeg : Z) (maxc csz stj idxw : word) (chunks hs : list word)
    (j0 : list byte),
  let ek := EkNew full nx bsz cnt maxc csz stj idxw chunks spacebeg b hs in
  stk asegs m lo (bv_unsigned sp + -144) -> ATOP <= lo -> lo <= bv_unsigned sp - 144 ->
  mem_inv asegs m ->
  a2 = Z_to_bv 64 (t + 208) ->
  (* [comment removed for export] *)
  rw_cells asegs m (bv_unsigned sp + -80) [C8 a2; C8 a3; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m (bv_unsigned sp + -144)
     [CB 8 j0; C8 (Z_to_bv 64 hm); C8 a2; C8 a3; C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 (t + 80)); C8 (Z_to_bv 64 0xab270); C8 (Z_to_bv 64 0x38198)] ->
  (* [comment removed for export] *)
  rw_cells asegs m 0xab2b0 [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->
  (* [comment removed for export] *)
  rw_cells asegs m hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  1 <= n <= Q_MAX -> hm mod 16 = 0 -> ablk hm (hm + 16 + rup n 8) -> tclr hm 24 -> hm + 16 + rup n 8 <= ATOP -> hm + 16 <= ATOP ->
  rw_cells asegs m (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) (repeat (Z_to_bv 8 253) (Z.to_nat (shlen (rup n 8))))] ->
  (* [comment removed for export] *)
  rw_cells asegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= qb -> qb + n + 8192 < 2^62 -> 0 <= fst0 < 2^64 -> 0 <= lst < 2^64 ->
  sclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> t mod 4096 = 0 -> (hm + 16 <= t \/ t + 4096 <= hm) ->
  (* [comment removed for export] *)
  (if full then 0 < nb /\ rw_cells asegs m lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)]
             /\ 0 <= nx < 2^64 /\ 0 <= bsz < 2^64 /\ 0x10007fff8000 <= lst /\ lst + 8192 <= ATOP
             /\ u64arr asegs m (lst + 24) hs /\ length hs = 1021%nat
             /\ rng RNG lst 8192
   else nb = 0 /\ lst = 0) ->
  rw_cells asegs m 0xaafb8 [C8 (Z_to_bv 64 spacebeg)] ->
  rw_cells asegs m (t + 2128) [C4 (Z_to_bv 64 cnt); C4 maxc; C8 csz] ->
  u32arr asegs m (t + 2128 + 16) chunks -> length chunks = 16%nat ->
  0 < cnt <= 16 -> nth_error chunks (Z.to_nat (cnt - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
  rw_cells asegs m (t + 2784) [C8 stj] ->
  b = spacebeg + 24 * 2^32 + 16 * bv_unsigned idxw ->
  (exists bs, rw_cells asegs m b [CB (Z.to_nat 8192) bs]) ->
  0 < spacebeg -> 0x10007fff8000 <= b -> b + 8192 <= ATOP ->
  (t + 4096 <= b \/ b + 8192 <= t) -> (t + 4096 <= lst \/ lst + 8192 <= t \/ lst = 0) -> (b + 8192 <= lst \/ lst + 8192 <= b) ->
  (hm + 16 <= b \/ b + 8192 <= hm) -> (hm + 16 <= lst \/ lst + 8192 <= hm) ->
  rng RNG b 8192 ->
  (* [comment removed for export] *)
  dk_pre ek g RNG t lst hm (qb + ek_delta ek n) m ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 -> rng RNG hm 16 -> rng RNG (shad (hm + 16)) (shlen (rup n 8)) ->
  iclr t 4096 ->                                            (* [comment removed for export] *)
  evtF asegs RNG (put_tail_post ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n nb fst0 lst qb b1 actx lo m)
    (MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 (Z_to_bv 64 (t + 2128)) (Z_to_bv 64 (t + 208))
             (Z_to_bv 64 1) a1 a2' a3' a4 a5 a6 a7
             (Z_to_bv 64 hm) (Z_to_bv 64 (t + 80)) a3 (Z_to_bv 64 n) (Z_to_bv 64 Q_CACHE) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x382f8) fc None m (seg_rom asegs)).
Section Zd2.   (* [comment removed for export] *)
Variable full : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 0).
Variable g : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 1).
Variable t : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 2).
Variable hm : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 3).
Variable lst : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 4).
Variable b : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 5).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 6).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 7).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 8).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 9).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 10).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 11).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 12).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 13).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 14).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 15).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 16).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 17).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 18).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 19).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 20).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 21).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 22).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 23).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 24).
Variable ra0 : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 25).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 26).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 27).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 28).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 29).
Variable a2' : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 30).
Variable a3' : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 31).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 32).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 33).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 34).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 35).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 36).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 37).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 38).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 39).
Variable F : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 40).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 41).
Variable m : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 42).
Variable n : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 43).
Variable nb : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 44).
Variable fst0 : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 45).
Variable qb : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 46).
Variable b1 : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 47).
Variable actx : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 48).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 49).
Variable nx : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 50).
Variable bsz : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 51).
Variable cnt : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 52).
Variable spacebeg : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 53).
Variable maxc : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 54).
Variable csz : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 55).
Variable stj : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 56).
Variable idxw : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 57).
Variable chunks : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 58).
Variable hs : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 59).
Variable j0 : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 60).
#[using="Type"] Lemma put_from_refill_spec__body : ltac:(let T := type of (fun (h : put_from_refill_spec__stmt) => h full g t hm lst b RNG ra sp gp tp s0 s1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra0 t0 t1 t2 a1 a2' a3' a4 a5 a6 a7 t3 t4 t5 t6 F fc m n nb fst0 qb b1 actx lo nx bsz cnt spacebeg maxc csz stj idxw chunks hs j0) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (full, (g, (t, (hm, (lst, (b, (RNG, (ra, (sp, (gp, (tp, (s0, (s1, (a2, (a3, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (ra0, (t0, (t1, (t2, (a1, (a2', (a3', (a4, (a5, (a6, (a7, (t3, (t4, (t5, (t6, (F, (fc, (m, (n, (nb, (fst0, (qb, (b1, (actx, (lo, (nx, (bsz, (cnt, (spacebeg, (maxc, (csz, (stj, (idxw, (chunks, (hs, j0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) as _.
 cbv zeta. intros ST CEIL LO MI -> FRP FRE QK HD N AL HLO TCH HHI HCE SH' QC NB QB QBN FST LST T0 T1 TAL DHT
    FULL SB CR CH LCH CNT NTH IXS STS HB BJ SBP B0 BL1 DTB DTL DBL DHB DHL RB DK RIMG RTLS RSTK RT RH RSH TI.
  band_int TI. (pose proof (ablk_lin _ _ HLO) as ndP__; nd_pre ndP__ 4%nat; intros HL1 HL2 HL3 HL4; nd_post). unfold AIMG_HI in HL1. band_int HLO. band_lin. band_int T0.   (* [comment removed for export] *)
  assert (SHB : 2148238848 <= shad (hm + 16) /\ shad (hm + 16) + shlen (rup n 8) <= 0x10007fff8000).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold Q_MAX in N. Z.div_mod_to_equations. lia. }
  assert (RUP : n <= rup n 8 <= n + 7 /\ rup n 8 mod 8 = 0) by (clear; unfold rup; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
  assert (SHL : 0 < shlen (rup n 8) < 0x10000000) by (unfold shlen; rewrite Z.shiftr_div_pow2 by lia; unfold Q_MAX in N; Z.div_mod_to_equations; lia).
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (shad (hm + 16), shad (hm + 16) + shlen (rup n 8));
              (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792);
              (lst, lst + qsz lst); (b, b + 8192);      (* [comment removed for export] *)
              (0xab308, 0xab308 + 4); (0xab310, 0xab310 + 32); (dk_glst g lst, dk_glst g lst + 8)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  pose proof QK as QK0. rw_split QK0 1%nat QMX QK2. clear QK2.
  box DHT. box DTB. box DTL. box DBL. box DHB. box DHL.
  destruct BJ as [junkb BJ].
  destruct full; [(nd_pre FULL 9%nat; intros NB1 LB NX BSZ L0 L1 LA0 LEN0 RL; nd_post); nz_box LEN0 LEN0Z | destruct FULL as [NB0 LST0]];
  unfold dk_glst in *; cbn [ek_pre dk_pre ek_b ek_nb ek_fst ek_lst ek_delta] in *;
  (nd_pre DK 7%nat; intros MX GC GNB GQB GFST GLST DK'; nd_post);
  (destruct (g_drain g) eqn:EGD;
   [ (nd_pre DK' 3%nat; intros QB1 GQ GFULL; nd_post);
     destruct (g_full g) eqn:EGF;
     [(nd_pre GFULL 9%nat; intros G1 GLB G3 G4 G5 G6 G7 G8 G9; nd_post); box G5; box G6; box G7; box G8 | destruct GFULL as [GNB0 GLST0]]
   | rename DK' into QB1 ]);
  rewrite ?EGD in *; cbn [ek_pre dk_pre ek_b ek_nb ek_fst ek_lst ek_delta dk_glst] in *; unfold AIMG_HI in *.
  all: first [assert (QZE : qsz lst = 8192) by (apply qsz_pos; generalize L0; clear; intros; lia) | assert (QZE : qsz lst = 8) by (apply qsz_eq0; exact LST0)]; rewrite QZE in *.   (* [comment removed for export] *)
  - (* [comment removed for export] *)
    box HD. box CH. box SH'. box GLB. box LA0. box FRP.
    snapshot [(t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box LB. box QC.   (* [comment removed for export] *)
    box ST.
    lazymatch goal with |- evtF _ _ _ (MS (mkR _ (Z_to_bv 64 (bv_unsigned ?spv + ?k)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      assert (RS64 : rng RNG (bv_unsigned (Z_to_bv 64 (bv_unsigned spv + k))) 64) by (apply (rng_sub' _ _ _ _ _ RSTK); rewrite unsigned_lit by lia; lia) end.   (* [comment removed for export] *)
    call_sp (enqueue_from_refill_spec true t lst b RNG _ _ _ _ _ _ _
               (Z_to_bv 64 0x38198) (Z_to_bv 64 0xab270) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 n) a3 (Z_to_bv 64 (t + 208)) (Z_to_bv 64 hm)
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt spacebeg lo maxc csz stj idxw chunks j0);
      [unboxed ST| exact CEIL| lia| lia| exact MI| exact FRE| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | split; [lia|]; split; [unboxed LB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try assumption; lia
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia|].
    try clear RS64.
    clear BJ STS CR LB QC.   (* [comment removed for export] *)
    try rename MI0 into MI.
    replace (bv_unsigned sp + -144 + 64) with (bv_unsigned sp + -80) in * by lia.
    clear ST. match goal with H : stk asegs ?mm lo (bv_unsigned sp + -80) |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; ylia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; ylia). carry SH' MUe WMe ltac:(lia). carry LA0 MUe WMe ltac:(rewrite LEN0Z; ub DTL; ub DBL; ylia). carry GLB MUe WMe ltac:(ub G5; ub G7; ub G8; ylia). carry FRP MUe WMe ltac:(lia). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].
    (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].   (* [comment removed for export] *)
    step. step. step. step.                    (* [comment removed for export] *)
    box HD.  box PC3. box PC4. box PC5. box POST. box PC1. box STS'. box LA0.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0xab308, 0xab308 + 4); (0xab310, 0xab310 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GLB. box GC. box MX. box FRE. box CH.   (* [comment removed for export] *)
    box ST.
    step. call_sp (drain_norecycle_spec true t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (nb + 1) fst0 b (qb + (n + 8192)) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| lia| lia
      | exact QMX| split; [lia|]; split; [unboxed GLB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try lia; ub G5; ylia| exact TI| atop_facts; lia|].
    try clear ST.
    clear QC' GLB GC MX FRE CH.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT; ub G6; ylia). carry PC3 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; ylia). carry PC4 MUd WMd ltac:(cbn [length]; ub DTB; first [ub G8 | pose proof GLST0]; ylia). carry PC5 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; ylia). carry POST MUd WMd ltac:(ub DTL; first [ub G7 | pose proof GLST0]; ylia). carry PC1 MUd WMd ltac:(first [ub G5 | pose proof GLST0]; ylia). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; ylia). carry LA0 MUd WMd ltac:(rewrite LEN0Z; ub DTL; first [ub G7 | pose proof GLST0]; ylia). clear MUd WMd.
    do 10 step.
    release_frame FRP ST (bv_unsigned sp).
    unfold put_tail_post. rewrite ?QZE. unfold tcache_post, dk_post, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).   (* [comment removed for export] *)  all: try (eexists; eassumption).
  - (* [comment removed for export] *)
    box HD. box CH. box SH'. box LA0. box FRP.
    snapshot [(t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box LB. box QC.   (* [comment removed for export] *)
    box ST.
    lazymatch goal with |- evtF _ _ _ (MS (mkR _ (Z_to_bv 64 (bv_unsigned ?spv + ?k)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      assert (RS64 : rng RNG (bv_unsigned (Z_to_bv 64 (bv_unsigned spv + k))) 64) by (apply (rng_sub' _ _ _ _ _ RSTK); rewrite unsigned_lit by lia; lia) end.   (* [comment removed for export] *)
    call_sp (enqueue_from_refill_spec true t lst b RNG _ _ _ _ _ _ _
               (Z_to_bv 64 0x38198) (Z_to_bv 64 0xab270) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 n) a3 (Z_to_bv 64 (t + 208)) (Z_to_bv 64 hm)
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt spacebeg lo maxc csz stj idxw chunks j0);
      [unboxed ST| exact CEIL| lia| lia| exact MI| exact FRE| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | split; [lia|]; split; [unboxed LB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try assumption; lia
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia|].
    try clear RS64.
    clear BJ STS CR LB QC.   (* [comment removed for export] *)
    try rename MI0 into MI.
    replace (bv_unsigned sp + -144 + 64) with (bv_unsigned sp + -80) in * by lia.
    clear ST. match goal with H : stk asegs ?mm lo (bv_unsigned sp + -80) |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; ylia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; ylia). carry SH' MUe WMe ltac:(lia). carry LA0 MUe WMe ltac:(rewrite LEN0Z; ub DTL; ub DBL; ylia). carry FRP MUe WMe ltac:(lia). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].
    (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].   (* [comment removed for export] *)
    step. step. step. step.                    (* [comment removed for export] *)
    box HD.  box PC3. box PC4. box PC5. box POST. box PC1. box STS'. box LA0.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0xab308, 0xab308 + 4); (0xab310, 0xab310 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GC. box MX. box FRE.   (* [comment removed for export] *)
    box ST.
    step. call_sp (drain_norecycle_spec false t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (nb + 1) fst0 b (qb + (n + 8192)) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| lia| lia
      | exact QMX| exact GNB0| exact TI| atop_facts; lia| exact I|].
    try clear ST.
    clear QC' GC MX FRE.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT;  ylia). carry PC3 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; ylia). carry PC4 MUd WMd ltac:(cbn [length]; ub DTB; first [ub G8 | pose proof GLST0]; ylia). carry PC5 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; ylia). carry POST MUd WMd ltac:(ub DTL; first [ub G7 | pose proof GLST0]; ylia). carry PC1 MUd WMd ltac:(first [ub G5 | pose proof GLST0]; ylia). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; ylia). carry LA0 MUd WMd ltac:(rewrite LEN0Z; ub DTL; first [ub G7 | pose proof GLST0]; ylia). clear MUd WMd.
    do 10 step.
    release_frame FRP ST (bv_unsigned sp).
    unfold put_tail_post. rewrite ?QZE. unfold tcache_post, dk_post, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).   (* [comment removed for export] *)  all: try (eexists; eassumption).
  - (* [comment removed for export] *)
    box HD. box CH. box SH'. box LA0. box FRP.
    snapshot [(t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box LB. box QC.   (* [comment removed for export] *)
    box ST.
    lazymatch goal with |- evtF _ _ _ (MS (mkR _ (Z_to_bv 64 (bv_unsigned ?spv + ?k)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      assert (RS64 : rng RNG (bv_unsigned (Z_to_bv 64 (bv_unsigned spv + k))) 64) by (apply (rng_sub' _ _ _ _ _ RSTK); rewrite unsigned_lit by lia; lia) end.   (* [comment removed for export] *)
    call_sp (enqueue_from_refill_spec true t lst b RNG _ _ _ _ _ _ _
               (Z_to_bv 64 0x38198) (Z_to_bv 64 0xab270) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 n) a3 (Z_to_bv 64 (t + 208)) (Z_to_bv 64 hm)
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt spacebeg lo maxc csz stj idxw chunks j0);
      [unboxed ST| exact CEIL| lia| lia| exact MI| exact FRE| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | split; [lia|]; split; [unboxed LB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try assumption; lia
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia|].
    try clear RS64.
    clear BJ STS CR LB QC.   (* [comment removed for export] *)
    try rename MI0 into MI.
    replace (bv_unsigned sp + -144 + 64) with (bv_unsigned sp + -80) in * by lia.
    clear ST. match goal with H : stk asegs ?mm lo (bv_unsigned sp + -80) |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; ylia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; ylia). carry SH' MUe WMe ltac:(lia). carry LA0 MUe WMe ltac:(rewrite LEN0Z; ub DTL; ub DBL; ylia). carry FRP MUe WMe ltac:(lia). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].
    (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. if_cases KD; zify_cond KD; [exfalso; unfold Q_CACHE in *; lia|].   (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    do 10 step.
    release_frame FRP ST (bv_unsigned sp).
    unfold put_tail_post. rewrite ?QZE. unfold tcache_post, dk_post, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).   (* [comment removed for export] *)  all: try (eexists; eassumption).
  - (* [comment removed for export] *)
    box HD. box CH. box SH'. box GLB. box FRP.
    snapshot [(t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box QC.   (* [comment removed for export] *)
    box ST.
    lazymatch goal with |- evtF _ _ _ (MS (mkR _ (Z_to_bv 64 (bv_unsigned ?spv + ?k)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      assert (RS64 : rng RNG (bv_unsigned (Z_to_bv 64 (bv_unsigned spv + k))) 64) by (apply (rng_sub' _ _ _ _ _ RSTK); rewrite unsigned_lit by lia; lia) end.   (* [comment removed for export] *)
    call_sp (enqueue_from_refill_spec false t lst b RNG _ _ _ _ _ _ _
               (Z_to_bv 64 0x38198) (Z_to_bv 64 0xab270) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 n) a3 (Z_to_bv 64 (t + 208)) (Z_to_bv 64 hm)
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt spacebeg lo maxc csz stj idxw chunks j0);
      [unboxed ST| exact CEIL| lia| lia| exact MI| exact FRE| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | exact NB0
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia| exact I|].
    try clear RS64.
    clear BJ STS CR QC.   (* [comment removed for export] *)
    try rename MI0 into MI.
    replace (bv_unsigned sp + -144 + 64) with (bv_unsigned sp + -80) in * by lia.
    clear ST. match goal with H : stk asegs ?mm lo (bv_unsigned sp + -80) |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; ylia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; ylia). carry SH' MUe WMe ltac:(lia). carry GLB MUe WMe ltac:(ub G5; ub G7; ub G8; ylia). carry FRP MUe WMe ltac:(lia). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].
    (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].   (* [comment removed for export] *)
    step. step. step. step.                    (* [comment removed for export] *)
    box HD.  box PC3. box PC4. box PC5. box PC1. box STS'.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0xab308, 0xab308 + 4); (0xab310, 0xab310 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GLB. box GC. box MX. box FRE. box CH.   (* [comment removed for export] *)
    box ST.
    step. call_sp (drain_norecycle_spec true t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (nb + 1) b b (qb + (n + 8192)) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| lia| lia
      | exact QMX| split; [lia|]; split; [unboxed GLB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try lia; ub G5; ylia| exact TI| atop_facts; lia|].
    try clear ST.
    clear QC' GLB GC MX FRE CH.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT; ub G6; ylia). carry PC3 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; ylia). carry PC4 MUd WMd ltac:(cbn [length]; ub DTB; first [ub G8 | pose proof GLST0]; ylia). carry PC5 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; ylia). carry PC1 MUd WMd ltac:(first [ub G5 | pose proof GLST0]; ylia). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; ylia). clear MUd WMd.
    do 10 step.
    release_frame FRP ST (bv_unsigned sp).
    unfold put_tail_post. rewrite ?QZE. unfold tcache_post, dk_post, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).   (* [comment removed for export] *)  all: try (eexists; eassumption).
  - (* [comment removed for export] *)
    box HD. box CH. box SH'. box FRP.
    snapshot [(t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box QC.   (* [comment removed for export] *)
    box ST.
    lazymatch goal with |- evtF _ _ _ (MS (mkR _ (Z_to_bv 64 (bv_unsigned ?spv + ?k)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      assert (RS64 : rng RNG (bv_unsigned (Z_to_bv 64 (bv_unsigned spv + k))) 64) by (apply (rng_sub' _ _ _ _ _ RSTK); rewrite unsigned_lit by lia; lia) end.   (* [comment removed for export] *)
    call_sp (enqueue_from_refill_spec false t lst b RNG _ _ _ _ _ _ _
               (Z_to_bv 64 0x38198) (Z_to_bv 64 0xab270) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 n) a3 (Z_to_bv 64 (t + 208)) (Z_to_bv 64 hm)
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt spacebeg lo maxc csz stj idxw chunks j0);
      [unboxed ST| exact CEIL| lia| lia| exact MI| exact FRE| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | exact NB0
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia| exact I|].
    try clear RS64.
    clear BJ STS CR QC.   (* [comment removed for export] *)
    try rename MI0 into MI.
    replace (bv_unsigned sp + -144 + 64) with (bv_unsigned sp + -80) in * by lia.
    clear ST. match goal with H : stk asegs ?mm lo (bv_unsigned sp + -80) |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; ylia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; ylia). carry SH' MUe WMe ltac:(lia). carry FRP MUe WMe ltac:(lia). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].
    (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].   (* [comment removed for export] *)
    step. step. step. step.                    (* [comment removed for export] *)
    box HD.  box PC3. box PC4. box PC5. box PC1. box STS'.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0xab308, 0xab308 + 4); (0xab310, 0xab310 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GC. box MX. box FRE.   (* [comment removed for export] *)
    box ST.
    step. call_sp (drain_norecycle_spec false t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (nb + 1) b b (qb + (n + 8192)) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| lia| lia
      | exact QMX| exact GNB0| exact TI| atop_facts; lia| exact I|].
    try clear ST.
    clear QC' GC MX FRE.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT;  ylia). carry PC3 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; ylia). carry PC4 MUd WMd ltac:(cbn [length]; ub DTB; first [ub G8 | pose proof GLST0]; ylia). carry PC5 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; ylia). carry PC1 MUd WMd ltac:(first [ub G5 | pose proof GLST0]; ylia). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; ylia). clear MUd WMd.
    do 10 step.
    release_frame FRP ST (bv_unsigned sp).
    unfold put_tail_post. rewrite ?QZE. unfold tcache_post, dk_post, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).   (* [comment removed for export] *)  all: try (eexists; eassumption).
  - (* [comment removed for export] *)
    box HD. box CH. box SH'. box FRP.
    snapshot [(t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box QC.   (* [comment removed for export] *)
    box ST.
    lazymatch goal with |- evtF _ _ _ (MS (mkR _ (Z_to_bv 64 (bv_unsigned ?spv + ?k)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      assert (RS64 : rng RNG (bv_unsigned (Z_to_bv 64 (bv_unsigned spv + k))) 64) by (apply (rng_sub' _ _ _ _ _ RSTK); rewrite unsigned_lit by lia; lia) end.   (* [comment removed for export] *)
    call_sp (enqueue_from_refill_spec false t lst b RNG _ _ _ _ _ _ _
               (Z_to_bv 64 0x38198) (Z_to_bv 64 0xab270) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 n) a3 (Z_to_bv 64 (t + 208)) (Z_to_bv 64 hm)
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt spacebeg lo maxc csz stj idxw chunks j0);
      [unboxed ST| exact CEIL| lia| lia| exact MI| exact FRE| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | exact NB0
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia| exact I|].
    try clear RS64.
    clear BJ STS CR QC.   (* [comment removed for export] *)
    try rename MI0 into MI.
    replace (bv_unsigned sp + -144 + 64) with (bv_unsigned sp + -80) in * by lia.
    clear ST. match goal with H : stk asegs ?mm lo (bv_unsigned sp + -80) |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; ylia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; ylia). carry SH' MUe WMe ltac:(lia). carry FRP MUe WMe ltac:(lia). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].
    (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. if_cases KD; zify_cond KD; [exfalso; unfold Q_CACHE in *; lia|].   (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    do 10 step.
    release_frame FRP ST (bv_unsigned sp).
    unfold put_tail_post. rewrite ?QZE. unfold tcache_post, dk_post, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).   (* [comment removed for export] *)  all: try (eexists; eassumption).
Qed.
End Zd2.
#[using="Type"] Lemma put_from_refill_spec : ltac:(let t := eval cbv delta [put_from_refill_spec__stmt] in put_from_refill_spec__stmt in exact t).
Proof. exact put_from_refill_spec__body. Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_aenqueue.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_aenqueueR.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_adrain.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_aput.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tail.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac ag_arith := lazymatch goal with
  | |- Z.le _ _ => idtac | |- Z.lt _ _ => idtac | |- Z.ge _ _ => idtac | |- Z.gt _ _ => idtac
  | |- le _ _ => idtac | |- lt _ _ => idtac | |- ge _ _ => idtac | |- gt _ _ => idtac
  | |- @eq _ _ _ => idtac | |- not _ => idtac | |- and _ _ => idtac | |- or _ _ => idtac | |- False => idtac | |- True => idtac
  end.
(* [comment removed for export] *)
Local Ltac nz_box H HZ := lazymatch type of H with @length ?A ?l = ?n =>
  let z := eval vm_compute in (Z.of_nat n) in assert (HZ : Z.of_nat (@length A l) = z) by (rewrite H; reflexivity); box H end.
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
Local Ltac fp_cover8 := apply sub_fp_cover8; repeat (apply Forall_cons; [ cbn [fst snd]; first [left; fp_cheap8 | right; fp_find8c | right; fp_find8] | ]); apply Forall_nil.
(* [comment removed for export] *)
Local Ltac transport_call_munch_tac ::= first [ fp_cover8 | unfold sub_fp; cbn [outside]; first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs; intros; lia end | clear; intros; lia | intros; slia ] ].
(* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.
(* [comment removed for export] *)
Local Ltac with_sclr tac := idtac; match goal with H : sclr ?a ?n |- _ => with_band H tac | _ => tac end.  (* [comment removed for export] *)

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
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition put_to_refill_post (full : bool) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 : word) (F : bvmap 5 word) (fc : bv 32)
    (t hm n lo lst nx bsz : Z) (hs : list word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) m' (j0 : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x38360) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2
                  (Z_to_bv 64 (t + 2128)) (Z_to_bv 64 (t + 208))
                  (Z_to_bv 64 (t + 208)) (Z_to_bv 64 (t + 2128)) (Z_to_bv 64 0xab398) (Z_to_bv 64 K_BATCH_CLASS) a4 a5 a6 a7
                  (Z_to_bv 64 hm) (Z_to_bv 64 (t + 80)) a3 (Z_to_bv 64 n) (Z_to_bv 64 Q_CACHE) s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x38b40) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 144, bv_unsigned sp); (shad (hm + 16), shad (hm + 16) + shlen (rup n 8))]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -144)
    /\ rw_cells asegs m' (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) (repeat (Z_to_bv 8 253) (Z.to_nat (shlen (rup n 8))))]
    /\ rw_cells asegs m' (bv_unsigned sp + -80) [C8 a2; C8 a3; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' (bv_unsigned sp + -144)
         [CB 8 j0; C8 (Z_to_bv 64 hm); C8 a2; C8 a3; C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 (t + 80)); C8 (Z_to_bv 64 0xab670); C8 (Z_to_bv 64 0x38200)]
    /\ (if full then rw_cells asegs m' lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)] /\ u64arr asegs m' (lst + 24) hs else True).

Definition put_to_refill_spec__stmt : Prop := forall (full : bool) (t hm lst : Z) RNG
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n nb fst0 qb b1 actx lo nx bsz : Z) (maxc csz : word) (hs : list word) (sjunk : list byte),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 144 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 0xab670 -> a1 = Z_to_bv 64 (t + 80) -> a2 = Z_to_bv 64 (t + 208) -> a4 = Z_to_bv 64 hm -> a5 = Z_to_bv 64 n ->
  (* [comment removed for export] *)
  rw_cells asegs m 0xab6b0 [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->
  rw_cells asegs m 0xa5888 [C8 (Z_to_bv 64 AFLAGS)] ->
  rw_cells asegs m 0xac224 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->
  poison_cells m ->
  (* [comment removed for export] *)
  rw_cells asegs m hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  1 <= n <= Q_MAX -> 0 <= b1 < 256 -> hm mod 16 = 0 -> ablk hm (hm + 16 + rup n 8) -> tclr hm 24 -> hm + 16 + rup n 8 <= ATOP -> hm + 16 <= ATOP ->
  rw_cells asegs m (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) sjunk] ->
  (* [comment removed for export] *)
  rw_cells asegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= lst < 2^64 ->
  sclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> t mod 4096 = 0 -> (hm + 16 <= t \/ t + 4096 <= hm) ->
  (* [comment removed for export] *)
  (if full then 0 < nb /\ rw_cells asegs m lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)]
             /\ 0x10007fff8000 <= lst /\ lst + 8192 <= ATOP
             /\ u64arr asegs m (lst + 24) hs /\ length hs = 1021%nat /\ rng RNG lst 8192
   else nb = 0 /\ lst = 0) ->
  rw_cells asegs m (t + 2128) [C4 (Z_to_bv 64 0); C4 maxc; C8 csz] ->
  (t + 4096 <= lst \/ lst + 8192 <= t \/ lst = 0) -> (hm + 16 <= lst \/ lst + 8192 <= hm) ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 -> rng RNG hm 16 -> rng RNG (shad (hm + 16)) (shlen (rup n 8)) ->
  iclr t 4096 ->                                            (* [comment removed for export] *)
  evtF asegs RNG (put_to_refill_post full ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 F fc t hm n lo lst nx bsz hs m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3805c) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable full : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 0).
Variable t : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 1).
Variable hm : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 2).
Variable lst : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 3).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 4).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 5).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 6).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 7).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 8).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 9).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 10).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 11).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 12).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 13).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 14).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 15).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 16).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 17).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 18).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 19).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 20).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 21).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 22).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 23).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 24).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 25).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 26).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 27).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 28).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 29).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 30).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 31).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 32).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 33).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 34).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 35).
Variable F : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 36).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 37).
Variable m : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 38).
Variable n : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 39).
Variable nb : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 40).
Variable fst0 : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 41).
Variable qb : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 42).
Variable b1 : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 43).
Variable actx : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 44).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 45).
Variable nx : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 46).
Variable bsz : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 47).
Variable maxc : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 48).
Variable csz : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 49).
Variable hs : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 50).
Variable sjunk : ltac2:(SecDietF.SzSecF.ty 'put_to_refill_spec__stmt 51).
#[using="Type"] Lemma put_to_refill_spec__body : ltac:(let T := type of (fun (h : put_to_refill_spec__stmt) => h full t hm lst RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n nb fst0 qb b1 actx lo nx bsz maxc csz hs sjunk) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (full, (t, (hm, (lst, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (n, (nb, (fst0, (qb, (b1, (actx, (lo, (nx, (bsz, (maxc, (csz, (hs, sjunk)))))))))))))))))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO MI -> -> -> -> -> QK GF FLG PC HD N B1 AL HLO TCH HHI HCE SH QC NB LST T0 T1 TAL DHT FULL CR DTL DHL RIMG RTLS RSTK RT RH RSH TI.
  band_int TI. (pose proof (ablk_lin _ _ HLO) as ndP__; nd_pre ndP__ 4%nat; intros HL1 HL2 HL3 HL4; nd_post). unfold AIMG_HI in HL1. band_int HLO. band_lin. band_int T0.   (* [comment removed for export] *)
  assert (SHB : 2148239360 <= shad (hm + 16) /\ shad (hm + 16) + shlen (rup n 8) <= 0x10007fff8000).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold Q_MAX in N. Z.div_mod_to_equations. lia. }
  assert (RUP : n <= rup n 8 <= n + 7 /\ rup n 8 mod 8 = 0) by (clear; unfold rup; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
  assert (SHL : 0 < shlen (rup n 8) < 0x10000000) by (unfold shlen; rewrite Z.shiftr_div_pow2 by lia; unfold Q_MAX in N; Z.div_mod_to_equations; lia).
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (shad (hm + 16), shad (hm + 16) + shlen (rup n 8))]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  (nd_pre PC 7%nat; intros P1 P2 P3 P4 P5 P6 P7; nd_post).
  box DHT. box DTL. box DHL.
  destruct full; [(nd_pre FULL 7%nat; intros NB1 LB L0 L1 LA0 LEN0 RL; nd_post); nz_box LEN0 LEN0Z | destruct FULL as [NB0 LST0]];
  unfold AIMG_HI in *.
  - (* [comment removed for export] *)
    box ST.   (* [comment removed for export] *)
    call (putA_spec t hm n); try unboxed ST; try eassumption; try reflexivity; try (ag_arith; unfold Q_MAX, AIMG_HI in *; lia).
    try clear ST.
    rename POST into FRP.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end. try rename MI0 into MI.
    box SH.   (* [comment removed for export] *)
    box ST.
    step. call_sp (poison_shadow_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (hm + 16) (rup n 8) 253 lo sjunk);
      [unboxed ST| exact CEIL| lia| exact MI| repeat (split; [assumption|]); assumption| reflexivity| reflexivity| reflexivity
      | Z.div_mod_to_equations; lia| lia| lia| first [assumption | (eapply ablk_sub; [exact HLO| clear; lia| clear; lia]) | unfold ablk; right; lia | unfold ablk; left; lia]| lia| lia| lia| unboxed SH|].
    try clear ST.
    clear SH.   (* [comment removed for export] *)
    try rename MI0 into MI. clear P1 P2 P3 P4 P5 P6 P7.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    match goal with H : rw_cells asegs ?mm (shad (hm + 16)) _ |- _ => rename H into SH' end.
    do 5 step.                                 (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    box HD. box SH'. box LA0. box LB. box FRP.
    snapshot [(bv_unsigned sp + -80 - 64, bv_unsigned sp + -80)]%Z MUe WMe.
    box ST.
    call_sp (enqueue_to_refill_spec true t lst RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz lo maxc csz);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| reflexivity| reflexivity| exact QC| lia| lia
      | split; [lia|]; split; [ub LB; exact Y|]; split; [unfold AIMG_HI; lia|]; split; [unfold Q_BATCH_BYTES; lia| exact RL]
      | exact CR| exact TI| atop_facts; lia| exact TAL| ub DTL; unfold Q_BATCH_BYTES; lia|].
    try clear ST.
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(lia). carry SH' MUe WMe ltac:(lia). carry LA0 MUe WMe ltac:(rewrite LEN0Z; lia). carry LB MUe WMe ltac:(lia). carry FRP MUe WMe ltac:(lia). clear MUe WMe.
    replace (bv_unsigned sp + -80 + -64) with (bv_unsigned sp + -144) in * by lia.
    unfold put_to_refill_post. finish.
    all: try assumption. all: try eassumption. all: try exact I. all: try (split; assumption).
  - (* [comment removed for export] *)
    box ST.   (* [comment removed for export] *)
    call (putA_spec t hm n); try unboxed ST; try eassumption; try reflexivity; try (ag_arith; unfold Q_MAX, AIMG_HI in *; lia).
    try clear ST.
    rename POST into FRP.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end. try rename MI0 into MI.
    box SH.   (* [comment removed for export] *)
    box ST.
    step. call_sp (poison_shadow_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (hm + 16) (rup n 8) 253 lo sjunk);
      [unboxed ST| exact CEIL| lia| exact MI| repeat (split; [assumption|]); assumption| reflexivity| reflexivity| reflexivity
      | Z.div_mod_to_equations; lia| lia| lia| first [assumption | (eapply ablk_sub; [exact HLO| clear; lia| clear; lia]) | unfold ablk; right; lia | unfold ablk; left; lia]| lia| lia| lia| unboxed SH|].
    try clear ST.
    clear SH.   (* [comment removed for export] *)
    try rename MI0 into MI. clear P1 P2 P3 P4 P5 P6 P7.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    match goal with H : rw_cells asegs ?mm (shad (hm + 16)) _ |- _ => rename H into SH' end.
    do 5 step.
    step.
    box HD. box SH'. box FRP.
    snapshot [(bv_unsigned sp + -80 - 64, bv_unsigned sp + -80)]%Z MUe WMe.
    box ST.
    call_sp (enqueue_to_refill_spec false t lst RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz lo maxc csz);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| reflexivity| reflexivity| exact QC| lia| lia
      | exact NB0
      | exact CR| exact TI| atop_facts; lia| exact TAL| ub DTL; unfold Q_BATCH_BYTES; lia|].
    try clear ST.
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(lia). carry SH' MUe WMe ltac:(lia). carry FRP MUe WMe ltac:(lia). clear MUe WMe.
    replace (bv_unsigned sp + -80 + -64) with (bv_unsigned sp + -144) in * by lia.
    unfold put_to_refill_post. finish.
    all: try assumption. all: try eassumption. all: try exact I.
Qed.
End Zd1.
#[using="Type"] Lemma put_to_refill_spec : ltac:(let t := eval cbv delta [put_to_refill_spec__stmt] in put_to_refill_spec__stmt in exact t).
Proof. exact put_to_refill_spec__body. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition put_from_refill_spec__stmt : Prop := forall (full : bool) (g : gqd) (t hm lst b : Z) RNG
    (ra sp gp tp s0 s1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (ra0 t0 t1 t2 a1 a2' a3' a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : amem) (n nb fst0 qb b1 actx lo nx bsz cnt spacebeg : Z) (maxc csz stj idxw : word) (chunks hs : list word)
    (j0 : list byte),
  let ek := EkNew full nx bsz cnt maxc csz stj idxw chunks spacebeg b hs in
  stk asegs m lo (bv_unsigned sp + -144) -> ATOP <= lo -> lo <= bv_unsigned sp - 144 ->
  mem_inv asegs m ->
  a2 = Z_to_bv 64 (t + 208) ->
  (* [comment removed for export] *)
  rw_cells asegs m (bv_unsigned sp + -80) [C8 a2; C8 a3; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m (bv_unsigned sp + -144)
     [CB 8 j0; C8 (Z_to_bv 64 hm); C8 a2; C8 a3; C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 (t + 80)); C8 (Z_to_bv 64 0xab670); C8 (Z_to_bv 64 0x38200)] ->
  (* [comment removed for export] *)
  rw_cells asegs m 0xab6b0 [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->
  (* [comment removed for export] *)
  rw_cells asegs m hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  1 <= n <= Q_MAX -> hm mod 16 = 0 -> ablk hm (hm + 16 + rup n 8) -> tclr hm 24 -> hm + 16 + rup n 8 <= ATOP -> hm + 16 <= ATOP ->
  rw_cells asegs m (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) (repeat (Z_to_bv 8 253) (Z.to_nat (shlen (rup n 8))))] ->
  (* [comment removed for export] *)
  rw_cells asegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= qb -> qb + n + 8192 < 2^62 -> 0 <= fst0 < 2^64 -> 0 <= lst < 2^64 ->
  sclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> t mod 4096 = 0 -> (hm + 16 <= t \/ t + 4096 <= hm) ->
  (* [comment removed for export] *)
  (if full then 0 < nb /\ rw_cells asegs m lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)]
             /\ 0 <= nx < 2^64 /\ 0 <= bsz < 2^64 /\ 0x10007fff8000 <= lst /\ lst + 8192 <= ATOP
             /\ u64arr asegs m (lst + 24) hs /\ length hs = 1021%nat
             /\ rng RNG lst 8192
   else nb = 0 /\ lst = 0) ->
  rw_cells asegs m 0xab3b8 [C8 (Z_to_bv 64 spacebeg)] ->
  rw_cells asegs m (t + 2128) [C4 (Z_to_bv 64 cnt); C4 maxc; C8 csz] ->
  u32arr asegs m (t + 2128 + 16) chunks -> length chunks = 16%nat ->
  0 < cnt <= 16 -> nth_error chunks (Z.to_nat (cnt - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
  rw_cells asegs m (t + 2784) [C8 stj] ->
  b = spacebeg + 24 * 2^32 + 16 * bv_unsigned idxw ->
  (exists bs, rw_cells asegs m b [CB (Z.to_nat 8192) bs]) ->
  0 < spacebeg -> 0x10007fff8000 <= b -> b + 8192 <= ATOP ->
  (t + 4096 <= b \/ b + 8192 <= t) -> (t + 4096 <= lst \/ lst + 8192 <= t \/ lst = 0) -> (b + 8192 <= lst \/ lst + 8192 <= b) ->
  (hm + 16 <= b \/ b + 8192 <= hm) -> (hm + 16 <= lst \/ lst + 8192 <= hm) ->
  rng RNG b 8192 ->
  (* [comment removed for export] *)
  dk_pre ek g RNG t lst hm (qb + ek_delta ek n) m ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 -> rng RNG hm 16 -> rng RNG (shad (hm + 16)) (shlen (rup n 8)) ->
  iclr t 4096 ->                                            (* [comment removed for export] *)
  evtF asegs RNG (put_tail_post ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n nb fst0 lst qb b1 actx lo m)
    (MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 (Z_to_bv 64 (t + 2128)) (Z_to_bv 64 (t + 208))
             (Z_to_bv 64 1) a1 a2' a3' a4 a5 a6 a7
             (Z_to_bv 64 hm) (Z_to_bv 64 (t + 80)) a3 (Z_to_bv 64 n) (Z_to_bv 64 Q_CACHE) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x38360) fc None m (seg_rom asegs)).
Section Zd2.   (* [comment removed for export] *)
Variable full : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 0).
Variable g : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 1).
Variable t : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 2).
Variable hm : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 3).
Variable lst : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 4).
Variable b : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 5).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 6).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 7).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 8).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 9).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 10).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 11).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 12).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 13).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 14).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 15).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 16).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 17).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 18).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 19).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 20).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 21).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 22).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 23).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 24).
Variable ra0 : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 25).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 26).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 27).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 28).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 29).
Variable a2' : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 30).
Variable a3' : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 31).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 32).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 33).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 34).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 35).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 36).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 37).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 38).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 39).
Variable F : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 40).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 41).
Variable m : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 42).
Variable n : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 43).
Variable nb : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 44).
Variable fst0 : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 45).
Variable qb : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 46).
Variable b1 : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 47).
Variable actx : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 48).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 49).
Variable nx : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 50).
Variable bsz : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 51).
Variable cnt : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 52).
Variable spacebeg : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 53).
Variable maxc : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 54).
Variable csz : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 55).
Variable stj : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 56).
Variable idxw : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 57).
Variable chunks : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 58).
Variable hs : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 59).
Variable j0 : ltac2:(SecDietF.SzSecF.ty 'put_from_refill_spec__stmt 60).
#[using="Type"] Lemma put_from_refill_spec__body : ltac:(let T := type of (fun (h : put_from_refill_spec__stmt) => h full g t hm lst b RNG ra sp gp tp s0 s1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra0 t0 t1 t2 a1 a2' a3' a4 a5 a6 a7 t3 t4 t5 t6 F fc m n nb fst0 qb b1 actx lo nx bsz cnt spacebeg maxc csz stj idxw chunks hs j0) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (full, (g, (t, (hm, (lst, (b, (RNG, (ra, (sp, (gp, (tp, (s0, (s1, (a2, (a3, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (ra0, (t0, (t1, (t2, (a1, (a2', (a3', (a4, (a5, (a6, (a7, (t3, (t4, (t5, (t6, (F, (fc, (m, (n, (nb, (fst0, (qb, (b1, (actx, (lo, (nx, (bsz, (cnt, (spacebeg, (maxc, (csz, (stj, (idxw, (chunks, (hs, j0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) as _.
 cbv zeta. intros ST CEIL LO MI -> FRP FRE QK HD N AL HLO TCH HHI HCE SH' QC NB QB QBN FST LST T0 T1 TAL DHT
    FULL SB CR CH LCH CNT NTH IXS STS HB BJ SBP B0 BL1 DTB DTL DBL DHB DHL RB DK RIMG RTLS RSTK RT RH RSH TI.
  band_int TI. (pose proof (ablk_lin _ _ HLO) as ndP__; nd_pre ndP__ 4%nat; intros HL1 HL2 HL3 HL4; nd_post). unfold AIMG_HI in HL1. band_int HLO. band_lin. band_int T0.   (* [comment removed for export] *)
  assert (SHB : 2148239360 <= shad (hm + 16) /\ shad (hm + 16) + shlen (rup n 8) <= 0x10007fff8000).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold Q_MAX in N. Z.div_mod_to_equations. lia. }
  assert (RUP : n <= rup n 8 <= n + 7 /\ rup n 8 mod 8 = 0) by (clear; unfold rup; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
  assert (SHL : 0 < shlen (rup n 8) < 0x10000000) by (unfold shlen; rewrite Z.shiftr_div_pow2 by lia; unfold Q_MAX in N; Z.div_mod_to_equations; lia).
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (shad (hm + 16), shad (hm + 16) + shlen (rup n 8));
              (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792);
              (lst, lst + qsz lst); (b, b + 8192);      (* [comment removed for export] *)
              (0xab708, 0xab708 + 4); (0xab710, 0xab710 + 32); (dk_glst g lst, dk_glst g lst + 8)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  pose proof QK as QK0. rw_split QK0 1%nat QMX QK2. clear QK2.
  box DHT. box DTB. box DTL. box DBL. box DHB. box DHL.
  destruct BJ as [junkb BJ].
  destruct full; [(nd_pre FULL 9%nat; intros NB1 LB NX BSZ L0 L1 LA0 LEN0 RL; nd_post); nz_box LEN0 LEN0Z | destruct FULL as [NB0 LST0]];
  unfold dk_glst in *; cbn [ek_pre dk_pre ek_b ek_nb ek_fst ek_lst ek_delta] in *;
  (nd_pre DK 7%nat; intros MX GC GNB GQB GFST GLST DK'; nd_post);
  (destruct (g_drain g) eqn:EGD;
   [ (nd_pre DK' 3%nat; intros QB1 GQ GFULL; nd_post);
     destruct (g_full g) eqn:EGF;
     [(nd_pre GFULL 9%nat; intros G1 GLB G3 G4 G5 G6 G7 G8 G9; nd_post); box G5; box G6; box G7; box G8 | destruct GFULL as [GNB0 GLST0]]
   | rename DK' into QB1 ]);
  rewrite ?EGD in *; cbn [ek_pre dk_pre ek_b ek_nb ek_fst ek_lst ek_delta dk_glst] in *; unfold AIMG_HI in *.
  all: first [assert (QZE : qsz lst = 8192) by (apply qsz_pos; generalize L0; clear; intros; lia) | assert (QZE : qsz lst = 8) by (apply qsz_eq0; exact LST0)]; rewrite QZE in *.   (* [comment removed for export] *)
  - (* [comment removed for export] *)
    box HD. box CH. box SH'. box GLB. box LA0. box FRP.
    snapshot [(t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box LB. box QC.   (* [comment removed for export] *)
    box ST.
    lazymatch goal with |- evtF _ _ _ (MS (mkR _ (Z_to_bv 64 (bv_unsigned ?spv + ?k)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      assert (RS64 : rng RNG (bv_unsigned (Z_to_bv 64 (bv_unsigned spv + k))) 64) by (apply (rng_sub' _ _ _ _ _ RSTK); rewrite unsigned_lit by lia; lia) end.   (* [comment removed for export] *)
    call_sp (enqueue_from_refill_spec true t lst b RNG _ _ _ _ _ _ _
               (Z_to_bv 64 0x38200) (Z_to_bv 64 0xab670) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 n) a3 (Z_to_bv 64 (t + 208)) (Z_to_bv 64 hm)
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt spacebeg lo maxc csz stj idxw chunks j0);
      [unboxed ST| exact CEIL| lia| lia| exact MI| exact FRE| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | split; [lia|]; split; [unboxed LB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try assumption; lia
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia|].
    try clear RS64.
    clear BJ STS CR LB QC.   (* [comment removed for export] *)
    try rename MI0 into MI.
    replace (bv_unsigned sp + -144 + 64) with (bv_unsigned sp + -80) in * by lia.
    clear ST. match goal with H : stk asegs ?mm lo (bv_unsigned sp + -80) |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; ylia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; ylia). carry SH' MUe WMe ltac:(lia). carry LA0 MUe WMe ltac:(rewrite LEN0Z; ub DTL; ub DBL; ylia). carry GLB MUe WMe ltac:(ub G5; ub G7; ub G8; ylia). carry FRP MUe WMe ltac:(lia). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].
    (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].   (* [comment removed for export] *)
    step. step. step. step.                    (* [comment removed for export] *)
    box HD.  box PC3. box PC4. box PC5. box POST. box PC1. box STS'. box LA0.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0xab708, 0xab708 + 4); (0xab710, 0xab710 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GLB. box GC. box MX. box FRE. box CH.   (* [comment removed for export] *)
    box ST.
    step. call_sp (drain_norecycle_spec true t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (nb + 1) fst0 b (qb + (n + 8192)) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| lia| lia
      | exact QMX| split; [lia|]; split; [unboxed GLB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try lia; ub G5; ylia| exact TI| atop_facts; lia|].
    try clear ST.
    clear QC' GLB GC MX FRE CH.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT; ub G6; ylia). carry PC3 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; ylia). carry PC4 MUd WMd ltac:(cbn [length]; ub DTB; first [ub G8 | pose proof GLST0]; ylia). carry PC5 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; ylia). carry POST MUd WMd ltac:(ub DTL; first [ub G7 | pose proof GLST0]; ylia). carry PC1 MUd WMd ltac:(first [ub G5 | pose proof GLST0]; ylia). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; ylia). carry LA0 MUd WMd ltac:(rewrite LEN0Z; ub DTL; first [ub G7 | pose proof GLST0]; ylia). clear MUd WMd.
    do 10 step.
    release_frame FRP ST (bv_unsigned sp).
    unfold put_tail_post. rewrite ?QZE. unfold tcache_post, dk_post, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).   (* [comment removed for export] *)  all: try (eexists; eassumption).
  - (* [comment removed for export] *)
    box HD. box CH. box SH'. box LA0. box FRP.
    snapshot [(t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box LB. box QC.   (* [comment removed for export] *)
    box ST.
    lazymatch goal with |- evtF _ _ _ (MS (mkR _ (Z_to_bv 64 (bv_unsigned ?spv + ?k)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      assert (RS64 : rng RNG (bv_unsigned (Z_to_bv 64 (bv_unsigned spv + k))) 64) by (apply (rng_sub' _ _ _ _ _ RSTK); rewrite unsigned_lit by lia; lia) end.   (* [comment removed for export] *)
    call_sp (enqueue_from_refill_spec true t lst b RNG _ _ _ _ _ _ _
               (Z_to_bv 64 0x38200) (Z_to_bv 64 0xab670) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 n) a3 (Z_to_bv 64 (t + 208)) (Z_to_bv 64 hm)
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt spacebeg lo maxc csz stj idxw chunks j0);
      [unboxed ST| exact CEIL| lia| lia| exact MI| exact FRE| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | split; [lia|]; split; [unboxed LB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try assumption; lia
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia|].
    try clear RS64.
    clear BJ STS CR LB QC.   (* [comment removed for export] *)
    try rename MI0 into MI.
    replace (bv_unsigned sp + -144 + 64) with (bv_unsigned sp + -80) in * by lia.
    clear ST. match goal with H : stk asegs ?mm lo (bv_unsigned sp + -80) |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; ylia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; ylia). carry SH' MUe WMe ltac:(lia). carry LA0 MUe WMe ltac:(rewrite LEN0Z; ub DTL; ub DBL; ylia). carry FRP MUe WMe ltac:(lia). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].
    (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].   (* [comment removed for export] *)
    step. step. step. step.                    (* [comment removed for export] *)
    box HD.  box PC3. box PC4. box PC5. box POST. box PC1. box STS'. box LA0.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0xab708, 0xab708 + 4); (0xab710, 0xab710 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GC. box MX. box FRE.   (* [comment removed for export] *)
    box ST.
    step. call_sp (drain_norecycle_spec false t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (nb + 1) fst0 b (qb + (n + 8192)) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| lia| lia
      | exact QMX| exact GNB0| exact TI| atop_facts; lia| exact I|].
    try clear ST.
    clear QC' GC MX FRE.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT;  ylia). carry PC3 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; ylia). carry PC4 MUd WMd ltac:(cbn [length]; ub DTB; first [ub G8 | pose proof GLST0]; ylia). carry PC5 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; ylia). carry POST MUd WMd ltac:(ub DTL; first [ub G7 | pose proof GLST0]; ylia). carry PC1 MUd WMd ltac:(first [ub G5 | pose proof GLST0]; ylia). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; ylia). carry LA0 MUd WMd ltac:(rewrite LEN0Z; ub DTL; first [ub G7 | pose proof GLST0]; ylia). clear MUd WMd.
    do 10 step.
    release_frame FRP ST (bv_unsigned sp).
    unfold put_tail_post. rewrite ?QZE. unfold tcache_post, dk_post, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).   (* [comment removed for export] *)  all: try (eexists; eassumption).
  - (* [comment removed for export] *)
    box HD. box CH. box SH'. box LA0. box FRP.
    snapshot [(t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box LB. box QC.   (* [comment removed for export] *)
    box ST.
    lazymatch goal with |- evtF _ _ _ (MS (mkR _ (Z_to_bv 64 (bv_unsigned ?spv + ?k)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      assert (RS64 : rng RNG (bv_unsigned (Z_to_bv 64 (bv_unsigned spv + k))) 64) by (apply (rng_sub' _ _ _ _ _ RSTK); rewrite unsigned_lit by lia; lia) end.   (* [comment removed for export] *)
    call_sp (enqueue_from_refill_spec true t lst b RNG _ _ _ _ _ _ _
               (Z_to_bv 64 0x38200) (Z_to_bv 64 0xab670) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 n) a3 (Z_to_bv 64 (t + 208)) (Z_to_bv 64 hm)
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt spacebeg lo maxc csz stj idxw chunks j0);
      [unboxed ST| exact CEIL| lia| lia| exact MI| exact FRE| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | split; [lia|]; split; [unboxed LB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try assumption; lia
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia|].
    try clear RS64.
    clear BJ STS CR LB QC.   (* [comment removed for export] *)
    try rename MI0 into MI.
    replace (bv_unsigned sp + -144 + 64) with (bv_unsigned sp + -80) in * by lia.
    clear ST. match goal with H : stk asegs ?mm lo (bv_unsigned sp + -80) |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; ylia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; ylia). carry SH' MUe WMe ltac:(lia). carry LA0 MUe WMe ltac:(rewrite LEN0Z; ub DTL; ub DBL; ylia). carry FRP MUe WMe ltac:(lia). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].
    (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. if_cases KD; zify_cond KD; [exfalso; unfold Q_CACHE in *; lia|].   (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    do 10 step.
    release_frame FRP ST (bv_unsigned sp).
    unfold put_tail_post. rewrite ?QZE. unfold tcache_post, dk_post, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).   (* [comment removed for export] *)  all: try (eexists; eassumption).
  - (* [comment removed for export] *)
    box HD. box CH. box SH'. box GLB. box FRP.
    snapshot [(t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box QC.   (* [comment removed for export] *)
    box ST.
    lazymatch goal with |- evtF _ _ _ (MS (mkR _ (Z_to_bv 64 (bv_unsigned ?spv + ?k)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      assert (RS64 : rng RNG (bv_unsigned (Z_to_bv 64 (bv_unsigned spv + k))) 64) by (apply (rng_sub' _ _ _ _ _ RSTK); rewrite unsigned_lit by lia; lia) end.   (* [comment removed for export] *)
    call_sp (enqueue_from_refill_spec false t lst b RNG _ _ _ _ _ _ _
               (Z_to_bv 64 0x38200) (Z_to_bv 64 0xab670) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 n) a3 (Z_to_bv 64 (t + 208)) (Z_to_bv 64 hm)
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt spacebeg lo maxc csz stj idxw chunks j0);
      [unboxed ST| exact CEIL| lia| lia| exact MI| exact FRE| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | exact NB0
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia| exact I|].
    try clear RS64.
    clear BJ STS CR QC.   (* [comment removed for export] *)
    try rename MI0 into MI.
    replace (bv_unsigned sp + -144 + 64) with (bv_unsigned sp + -80) in * by lia.
    clear ST. match goal with H : stk asegs ?mm lo (bv_unsigned sp + -80) |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; ylia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; ylia). carry SH' MUe WMe ltac:(lia). carry GLB MUe WMe ltac:(ub G5; ub G7; ub G8; ylia). carry FRP MUe WMe ltac:(lia). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].
    (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].   (* [comment removed for export] *)
    step. step. step. step.                    (* [comment removed for export] *)
    box HD.  box PC3. box PC4. box PC5. box PC1. box STS'.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0xab708, 0xab708 + 4); (0xab710, 0xab710 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GLB. box GC. box MX. box FRE. box CH.   (* [comment removed for export] *)
    box ST.
    step. call_sp (drain_norecycle_spec true t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (nb + 1) b b (qb + (n + 8192)) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| lia| lia
      | exact QMX| split; [lia|]; split; [unboxed GLB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try lia; ub G5; ylia| exact TI| atop_facts; lia|].
    try clear ST.
    clear QC' GLB GC MX FRE CH.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT; ub G6; ylia). carry PC3 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; ylia). carry PC4 MUd WMd ltac:(cbn [length]; ub DTB; first [ub G8 | pose proof GLST0]; ylia). carry PC5 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; ylia). carry PC1 MUd WMd ltac:(first [ub G5 | pose proof GLST0]; ylia). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; ylia). clear MUd WMd.
    do 10 step.
    release_frame FRP ST (bv_unsigned sp).
    unfold put_tail_post. rewrite ?QZE. unfold tcache_post, dk_post, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).   (* [comment removed for export] *)  all: try (eexists; eassumption).
  - (* [comment removed for export] *)
    box HD. box CH. box SH'. box FRP.
    snapshot [(t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box QC.   (* [comment removed for export] *)
    box ST.
    lazymatch goal with |- evtF _ _ _ (MS (mkR _ (Z_to_bv 64 (bv_unsigned ?spv + ?k)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      assert (RS64 : rng RNG (bv_unsigned (Z_to_bv 64 (bv_unsigned spv + k))) 64) by (apply (rng_sub' _ _ _ _ _ RSTK); rewrite unsigned_lit by lia; lia) end.   (* [comment removed for export] *)
    call_sp (enqueue_from_refill_spec false t lst b RNG _ _ _ _ _ _ _
               (Z_to_bv 64 0x38200) (Z_to_bv 64 0xab670) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 n) a3 (Z_to_bv 64 (t + 208)) (Z_to_bv 64 hm)
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt spacebeg lo maxc csz stj idxw chunks j0);
      [unboxed ST| exact CEIL| lia| lia| exact MI| exact FRE| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | exact NB0
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia| exact I|].
    try clear RS64.
    clear BJ STS CR QC.   (* [comment removed for export] *)
    try rename MI0 into MI.
    replace (bv_unsigned sp + -144 + 64) with (bv_unsigned sp + -80) in * by lia.
    clear ST. match goal with H : stk asegs ?mm lo (bv_unsigned sp + -80) |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; ylia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; ylia). carry SH' MUe WMe ltac:(lia). carry FRP MUe WMe ltac:(lia). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].
    (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].   (* [comment removed for export] *)
    step. step. step. step.                    (* [comment removed for export] *)
    box HD.  box PC3. box PC4. box PC5. box PC1. box STS'.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0xab708, 0xab708 + 4); (0xab710, 0xab710 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GC. box MX. box FRE.   (* [comment removed for export] *)
    box ST.
    step. call_sp (drain_norecycle_spec false t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (nb + 1) b b (qb + (n + 8192)) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| lia| lia
      | exact QMX| exact GNB0| exact TI| atop_facts; lia| exact I|].
    try clear ST.
    clear QC' GC MX FRE.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT;  ylia). carry PC3 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; ylia). carry PC4 MUd WMd ltac:(cbn [length]; ub DTB; first [ub G8 | pose proof GLST0]; ylia). carry PC5 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; ylia). carry PC1 MUd WMd ltac:(first [ub G5 | pose proof GLST0]; ylia). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; ylia). clear MUd WMd.
    do 10 step.
    release_frame FRP ST (bv_unsigned sp).
    unfold put_tail_post. rewrite ?QZE. unfold tcache_post, dk_post, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).   (* [comment removed for export] *)  all: try (eexists; eassumption).
  - (* [comment removed for export] *)
    box HD. box CH. box SH'. box FRP.
    snapshot [(t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box QC.   (* [comment removed for export] *)
    box ST.
    lazymatch goal with |- evtF _ _ _ (MS (mkR _ (Z_to_bv 64 (bv_unsigned ?spv + ?k)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      assert (RS64 : rng RNG (bv_unsigned (Z_to_bv 64 (bv_unsigned spv + k))) 64) by (apply (rng_sub' _ _ _ _ _ RSTK); rewrite unsigned_lit by lia; lia) end.   (* [comment removed for export] *)
    call_sp (enqueue_from_refill_spec false t lst b RNG _ _ _ _ _ _ _
               (Z_to_bv 64 0x38200) (Z_to_bv 64 0xab670) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 n) a3 (Z_to_bv 64 (t + 208)) (Z_to_bv 64 hm)
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt spacebeg lo maxc csz stj idxw chunks j0);
      [unboxed ST| exact CEIL| lia| lia| exact MI| exact FRE| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | exact NB0
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia| exact I|].
    try clear RS64.
    clear BJ STS CR QC.   (* [comment removed for export] *)
    try rename MI0 into MI.
    replace (bv_unsigned sp + -144 + 64) with (bv_unsigned sp + -80) in * by lia.
    clear ST. match goal with H : stk asegs ?mm lo (bv_unsigned sp + -80) |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; ylia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; ylia). carry SH' MUe WMe ltac:(lia). carry FRP MUe WMe ltac:(lia). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].
    (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. if_cases KD; zify_cond KD; [exfalso; unfold Q_CACHE in *; lia|].   (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    do 10 step.
    release_frame FRP ST (bv_unsigned sp).
    unfold put_tail_post. rewrite ?QZE. unfold tcache_post, dk_post, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).   (* [comment removed for export] *)  all: try (eexists; eassumption).
Qed.
End Zd2.
#[using="Type"] Lemma put_from_refill_spec : ltac:(let t := eval cbv delta [put_from_refill_spec__stmt] in put_from_refill_spec__stmt in exact t).
Proof. exact put_from_refill_spec__body. Qed.
End CANSEC1.
End TwB.
End F_afree_tailR.

(* [comment removed for export] *)
Module F_afree_icptR.
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecSlog__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_adrain__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_front__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_tail. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_afree_iseg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_front OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tail OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_aenqueueR OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tailR__A3W.F_afree_tailR OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_icpt.
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
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section WithDepot.
Variable DI : ADepotIface.

Notation free_W L sp t hm n lst ek g :=
  ([(bv_unsigned sp - 4096, bv_unsigned sp); (0xaf800, 0xaf800 + 0x81030); (0x13e088, 0x13e088 + 4);
    (t + 3168, t + 3169); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608);
    (shad (hm + 16), shad (hm + 16) + shlen (rup n 8)); (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792);
    (lst, lst + qsz lst); (ek_b ek lst, ek_b ek lst + 8192);
    (0xab308, 0xab308 + 4); (0xab310, 0xab310 + 32); (dk_glst g lst, dk_glst g lst + 8)]%Z) (only parsing).
Notation toref_W L sp t hm n :=
  ([(bv_unsigned sp - 4096, bv_unsigned sp); (0xaf800, 0xaf800 + 0x81030); (0x13e088, 0x13e088 + 4);
    (t + 3168, t + 3169); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608);
    (shad (hm + 16), shad (hm + 16) + shlen (rup n 8))]%Z) (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition free_to_refill_post (L : alayout) (full : bool)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t hm n b1 actx lo lst nx bsz : Z) (hs : list word) (trt : list Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (id : Z) (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) m' (sj' tb' : list word) (junk2 j0 : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x382f8) (Z_to_bv 64 (bv_unsigned sp + -2272)) gp tp t0 t1 t2
                  (Z_to_bv 64 (t + 2128)) (Z_to_bv 64 (t + 208))
                  (Z_to_bv 64 (t + 208)) (Z_to_bv 64 (t + 2128)) (Z_to_bv 64 0xaaf98) (Z_to_bv 64 K_BATCH_CLASS) a4 a5 a6 a7
                  (Z_to_bv 64 hm) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 n) (Z_to_bv 64 Q_CACHE)
                  s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x38ad8) fc None m' (seg_rom asegs)
    /\ munch (toref_W L sp t hm n) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -2272)
    /\ 0 < id < 2^31
    /\ rw_cells asegs m' hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)]
    /\ rw_cells asegs m' (hm + 16) [C8 (Z_to_bv 64 id)]
    /\ rw_cells asegs m' (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) (repeat (Z_to_bv 8 253) (Z.to_nat (shlen (rup n 8))))]
    /\ u64arr asegs m' (t + 2800) sj' /\ length sj' = 46%nat
    /\ rw_cells asegs m' (t + 3168) [C1 (Z_to_bv 8 0)]
    /\ rw_cells asegs m' 0x13e088 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ stk asegs m' 0xaf800 (0xaf800 + 0x81030)
    /\ (forall j, 0 <= j < 32768 -> bytes_at asegs m' (0xaf808 + 8 * j) (le8 (Z_to_bv 64 0)))
    (* [comment removed for export] *)
    /\ rw_cells asegs m' (bv_unsigned sp + -2128) [C8 (Z_to_bv 64 (bv_unsigned sp + -2128 + 16)); C4 (Z_to_bv 64 (1 + Z.of_nat (length trt))); C4 (Z_to_bv 64 0)]
    /\ u64arr asegs m' (bv_unsigned sp + -2128 + 16) tb' /\ length tb' = 255%nat
    /\ rw_cells asegs m' (bv_unsigned sp + -72) [C8 sp; CB 8 junk2; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' (bv_unsigned sp + -2208)
         [C8 (Z_to_bv 64 (t + 208)); C8 (Z_to_bv 64 (bv_unsigned sp + -2128)); C8 s6; C8 (Z_to_bv 64 (bv_unsigned sp + -81));
          C8 (Z_to_bv 64 (bv_unsigned sp + -2128)); C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 0x562bc); C8 (Z_to_bv 64 (hm + 16)); C8 sp; C8 (Z_to_bv 64 0x5632c)]
    /\ rw_cells asegs m' (bv_unsigned sp + -2272)
         [CB 8 j0; C8 (Z_to_bv 64 hm); C8 (Z_to_bv 64 (t + 208)); C8 (Z_to_bv 64 (bv_unsigned sp + -2128)); C8 (Z_to_bv 64 n);
          C8 (Z_to_bv 64 (t + 80)); C8 (Z_to_bv 64 0xab270); C8 (Z_to_bv 64 0x38198)]
    /\ (if full then rw_cells asegs m' lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)] /\ u64arr asegs m' (lst + 24) hs else True)
    /\ ADEPOT DI L m'.

Definition free_to_refill_spec__stmt : Prop := forall (L : alayout) (ia full : bool) RNG
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem)
    (t ctx hm n b1 actx lo top bot nb fst0 lst qb nx bsz : Z) (uw maxc csz : word) (sj hs : list word) (sjunk : list byte) (trt : list Z),
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
  (if full then 0 < nb /\ rw_cells asegs m lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)]
             /\ 0x10007fff8000 <= lst /\ lst + 8192 <= ATOP
             /\ u64arr asegs m (lst + 24) hs /\ length hs = 1021%nat /\ rng RNG lst 8192
   else nb = 0 /\ lst = 0) ->
  rw_cells asegs m (t + 2128) [C4 (Z_to_bv 64 0); C4 maxc; C8 csz] ->
  (t + 4096 <= lst \/ lst + 8192 <= t \/ lst = 0) -> (hm + 24 <= lst \/ lst + 8192 <= hm) ->
  (al_nodes L + 1048576 <= lst \/ lst + 8192 <= al_nodes L) -> (al_store L + 8388608 <= lst \/ lst + 8192 <= al_store L) ->
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
  evtF asegs RNG (free_to_refill_post L full ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n b1 actx lo lst nx bsz hs trt m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 0).
Variable ia : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 1).
Variable full : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 2).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 3).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 4).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 5).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 6).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 7).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 8).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 9).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 10).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 11).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 12).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 13).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 14).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 15).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 16).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 17).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 18).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 19).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 20).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 21).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 22).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 23).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 24).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 25).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 26).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 27).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 28).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 29).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 30).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 31).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 32).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 33).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 34).
Variable F : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 35).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 36).
Variable m : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 37).
Variable t : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 38).
Variable ctx : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 39).
Variable hm : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 40).
Variable n : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 41).
Variable b1 : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 42).
Variable actx : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 43).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 44).
Variable top : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 45).
Variable bot : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 46).
Variable nb : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 47).
Variable fst0 : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 48).
Variable lst : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 49).
Variable qb : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 50).
Variable nx : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 51).
Variable bsz : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 52).
Variable uw : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 53).
Variable maxc : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 54).
Variable csz : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 55).
Variable sj : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 56).
Variable hs : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 57).
Variable sjunk : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 58).
Variable trt : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 59).
#[using="Type"] Lemma free_to_refill_spec__body : ltac:(let T := type of (fun (h : free_to_refill_spec__stmt) => h L ia full RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m t ctx hm n b1 actx lo top bot nb fst0 lst qb nx bsz uw maxc csz sj hs sjunk trt) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (ia, (full, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (t, (ctx, (hm, (n, (b1, (actx, (lo, (top, (bot, (nb, (fst0, (lst, (qb, (nx, (bsz, (uw, (maxc, (csz, (sj, (hs, (sjunk, trt)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) as _.

  intros ST CEIL LO MI TP Ha0 SP16 AC PC MCS CF34 GPG PGC HK QK GF FLG FL IAS IAM CT8 TT0 SW UW STATS LSJ QC NB QB QBN FST LST
         CX0 C0 C1 T0 T1 TAL CT2 HD HUW B1 B13 N AL HLO TCH HHI HCE SH DHT DHC FULL CR0 DTL DHL DNL DSL DEP N0 N1 R0 R1 DHN DHS DTN DTS DCN DCS XTNO XTST
         UNW S0NE TRU B0 BB BOTOP TOP RA4 RANE RIMG RTLS RSTK RCTX RT RNO RST RH RSH CI NI SI TI. band_lin.   (* [comment removed for export] *)
  band_int TI. (pose proof (ablk_lin _ _ HLO) as ndP__; nd_pre ndP__ 4%nat; intros HL1 HL2 HL3 HL4; nd_post). unfold AIMG_HI in HL1. band_int HLO. band_int C0. band_int T0. band_int N0. band_int R0.   (* [comment removed for export] *)
  pose proof (afree_unw_length _ _ _ _ _ _ _ _ UNW) as LTRT.
  pose proof (afree_unw_sp47 _ _ _ _ _ _ _ _ UNW ltac:(clear -TOP; lia)) as SP47.
  pose proof PC as PC'. destruct PC' as (GOT6 & _).
  assert (RUP : n <= rup n 8 <= n + 7 /\ rup n 8 mod 8 = 0) by (clear -N; unfold rup; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
  assert (SHB : 2148238848 <= shad (hm + 16) /\ shad (hm + 16) + shlen (rup n 8) <= 0x10007fff8000 /\ 0 < shlen (rup n 8)).
  { clear -N HLO HL1 HHI HCE. unfold shad, shlen, ASHOFF, rup in *. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold Q_MAX in *. Z.div_mod_to_equations. lia. }
  unfold AIMG_HI, AFREE_SYM, AFREE_PC in *.
  word_range sp SPR.
  box DHT. box DHC. box DHN. box DHS. box DTN. box DTS. box DCN. box DCS. box CT2. box DTL. box DHL. box DNL. box DSL.
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
  xport CR0 MUf WMf ltac:(ub DHT; ub DTN; ub DTS; ylia).
  assert (PC1 : poison_cells m1).
  { eapply poison_cells_frame2; [exact PC | exact MUf | exact WMf |].
    repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
  assert (FULL1 : if full then 0 < nb /\ rw_cells asegs m1 lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)]
             /\ 0x10007fff8000 <= lst /\ lst + 8192 <= ATOP
             /\ u64arr asegs m1 (lst + 24) hs /\ length hs = 1021%nat /\ rng RNG lst 8192
           else nb = 0 /\ lst = 0).
  { destruct full; [| exact FULL]. (nd_pre FULL 7%nat; intros NB1 LB L0 L1 LA0 LEN0 RL; nd_post).
    xport LB MUf WMf ltac:(ub DTL; ub DHL; ub DNL; ub DSL; ylia). xport LA0 MUf WMf ltac:(rewrite LEN0; ub DTL; ub DHL; ub DNL; ub DSL; ylia).
    split; [exact NB1|]. split; [exact LB|]. split; [exact L0|]. split; [exact L1|]. split; [exact LA0|]. split; [exact LEN0| exact RL]. }
  clear FULL PC.
  (* [comment removed for export] *)
  name_sp sp (-2128).
  eapply evtF_cut.
  { eapply (put_to_refill_spec full t hm lst RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 n nb fst0 qb b1 actx lo nx bsz maxc csz hs sjunk).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => rewrite Hsp; exact STf
         | |- mem_inv _ _ => exact MIf
         | |- poison_cells _ => exact PC1
         | |- @eq word _ _ => rewrite ?Esp; first [reflexivity | apply Z_to_bv_eqm; rewrite ?unsigned_lit by lia; lia]
         | |- if _ then _ else _ => exact FULL1
         | |- _ \/ _ => first [ub DHT; ylia | ub DTL; ylia | ub DHL; ylia]
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD1
         | |- rw_cells _ _ (shad _) _ => exact SH
         | |- rw_cells _ _ (_ + 80) _ => exact QC
         | |- rw_cells _ _ (_ + 2128) _ => exact CR0
         | |- iclr _ _ => exact TI
         end.
    all: try eassumption. all: try (unfold AIMG_HI, Q_MAX in *; lia).
    all: match goal with |- ?G => idtac "REMP" G end. }
  cbv beta. intros ms2 PP. unfold put_to_refill_post in PP.
  (nd_pre PP 14%nat; intros t0b t1b t2b a4b a5b a6b a7b t3b t4b t5b t6b m2 j0 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 8%nat; intros MUp WMp MIp STp SH2 FRP FRE LBS; nd_post).
  unname_sp. rewrite ?unsigned_lit in MUp by lia. rewrite ?unsigned_lit in STp by lia.
  rewrite ?unsigned_lit in FRP by lia. rewrite ?unsigned_lit in FRE by lia.
  replace (bv_unsigned sp + -2128 + -80) with (bv_unsigned sp + -2208) in * by lia.
  replace (bv_unsigned sp + -2128 + -144) with (bv_unsigned sp + -2272) in * by lia.
  (* [comment removed for export] *)
  xport HD1 MUp WMp ltac:(lia). xport FC1 MUp WMp ltac:(lia).
  xport STATS1 MUp WMp ltac:(rewrite LSJ1; lia).
  xport UW1 MUp WMp ltac:(lia).
  xport FL1 MUp WMp ltac:(lia). xport IAS1 MUp WMp ltac:(lia).
  xport SS1 MUp WMp ltac:(lia). xport TB1 MUp WMp ltac:(rewrite LTB1; lia). xport FRS1 MUp WMp ltac:(lia).
  assert (IAM2 : forall j, 0 <= j < 32768 -> bytes_at asegs m2 (0xaf808 + 8 * j) (le8 (Z_to_bv 64 0))).
  { (intros j Hj; eapply bytes_at_agree; [exact (IAM1 j Hj)|];
    intros i Hi; apply MUp; cbn [outside]; rewrite length_le8 in Hi; rewrite wa_unsigned by lia; lia). }
  clear IAM1.
  assert (DEP2 : ADEPOT DI L m2).
  { eapply (adi_frame DI); [exact DEP1 | exact MUp | exact WMp |].
    (repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq; first [lia | ub DTN; ub DTS; ylia] |]); apply Forall_nil). }
  clear DEP1.
  (* [comment removed for export] *)
  assert (MU : munch (toref_W L sp t hm n) m m2).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUp]].
    eapply munch_weaken; [| exact MUf].
    all: solve_sub_fp sp. }
  assert (WM : wmono asegs m m2) by (eapply wmono_trans; [exact WMf| exact WMp]).
  apply evtF_done. unfold free_to_refill_post. exists id. do 11 eexists. exists m2, sj1, tb1, junk2, j0.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MIp|]. split; [exact STp|]. split; [exact IDR|].
  split; [exact HD1|]. split; [exact FC1|]. split; [exact SH2|].
  split; [exact STATS1|]. split; [exact LSJ1|]. split; [exact UW1|]. split; [exact FL1|]. split; [exact IAS1|]. split; [exact IAM2|].
  split; [exact SS1|]. split; [exact TB1|]. split; [exact LTB1|]. split; [exact FRS1|]. split; [exact FRP|]. split; [exact FRE|].
  split; [exact LBS|]. exact DEP2.
  Unshelve. all: try exact STf; try exact STp.
Qed.
End Zd1.
#[using="Type"] Lemma free_to_refill_spec : ltac:(let t := eval cbv delta [free_to_refill_spec__stmt] in free_to_refill_spec__stmt in exact t).
Proof. exact free_to_refill_spec__body. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition free_from_refill_spec__stmt : Prop := forall (L : alayout) (full : bool) (g : gqd) RNG
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : amem)
    (t hm n b1 actx lo nb fst0 lst qb nx bsz cnt spacebeg id b : Z) (maxc csz stj idxw : word) (sj tb chunks hs : list word)
    (junk2 j0 : list byte) (trt : list Z),
  let ek := EkNew full nx bsz cnt maxc csz stj idxw chunks spacebeg b hs in
  stk asegs m lo (bv_unsigned sp + -2272) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
  mem_inv asegs m ->
  (* [comment removed for export] *)
  rw_cells asegs m (bv_unsigned sp + -2128) [C8 (Z_to_bv 64 (bv_unsigned sp + -2128 + 16)); C4 (Z_to_bv 64 (1 + Z.of_nat (length trt))); C4 (Z_to_bv 64 0)] ->
  u64arr asegs m (bv_unsigned sp + -2128 + 16) tb -> length tb = 255%nat ->
  rw_cells asegs m (bv_unsigned sp + -72) [C8 sp; CB 8 junk2; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m (bv_unsigned sp + -2208)
     [C8 (Z_to_bv 64 (t + 208)); C8 (Z_to_bv 64 (bv_unsigned sp + -2128)); C8 s6; C8 (Z_to_bv 64 (bv_unsigned sp + -81));
      C8 (Z_to_bv 64 (bv_unsigned sp + -2128)); C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 0x562bc); C8 (Z_to_bv 64 (hm + 16)); C8 sp; C8 (Z_to_bv 64 0x5632c)] ->
  rw_cells asegs m (bv_unsigned sp + -2272)
     [CB 8 j0; C8 (Z_to_bv 64 hm); C8 (Z_to_bv 64 (t + 208)); C8 (Z_to_bv 64 (bv_unsigned sp + -2128)); C8 (Z_to_bv 64 n);
      C8 (Z_to_bv 64 (t + 80)); C8 (Z_to_bv 64 0xab270); C8 (Z_to_bv 64 0x38198)] ->
  (* [comment removed for export] *)
  rw_cells asegs m 0xab2b0 [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->
  (* [comment removed for export] *)
  rw_cells asegs m hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  rw_cells asegs m (hm + 16) [C8 (Z_to_bv 64 id)] -> 0 < id < 2^31 ->
  1 <= n <= Q_MAX -> hm mod 16 = 0 -> ablk hm (hm + 16 + rup n 8) -> tclr hm 24 -> hm + 16 + rup n 8 <= ATOP -> hm + 24 <= ATOP ->
  rw_cells asegs m (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) (repeat (Z_to_bv 8 253) (Z.to_nat (shlen (rup n 8))))] ->
  (* [comment removed for export] *)
  rw_cells asegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= qb -> qb + n + 8192 < 2^62 -> 0 <= fst0 < 2^64 -> 0 <= lst < 2^64 ->
  sclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> t mod 4096 = 0 -> (hm + 24 <= t \/ t + 4096 <= hm) ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat -> rw_cells asegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m 0x13e088 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  stk asegs m 0xaf800 (0xaf800 + 0x81030) ->
  (forall j, 0 <= j < 32768 -> bytes_at asegs m (0xaf808 + 8 * j) (le8 (Z_to_bv 64 0))) ->
  (* [comment removed for export] *)
  (if full then 0 < nb /\ rw_cells asegs m lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)]
             /\ 0 <= nx < 2^64 /\ 0 <= bsz < 2^64 /\ 0x10007fff8000 <= lst /\ lst + 8192 <= ATOP
             /\ u64arr asegs m (lst + 24) hs /\ length hs = 1021%nat
             /\ rng RNG lst 8192
   else nb = 0 /\ lst = 0) ->
  rw_cells asegs m 0xaafb8 [C8 (Z_to_bv 64 spacebeg)] ->
  rw_cells asegs m (t + 2128) [C4 (Z_to_bv 64 cnt); C4 maxc; C8 csz] ->
  u32arr asegs m (t + 2128 + 16) chunks -> length chunks = 16%nat ->
  0 < cnt <= 16 -> nth_error chunks (Z.to_nat (cnt - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
  rw_cells asegs m (t + 2784) [C8 stj] ->
  b = spacebeg + 24 * 2^32 + 16 * bv_unsigned idxw ->
  (exists bs, rw_cells asegs m b [CB (Z.to_nat 8192) bs]) ->
  0 < spacebeg -> 0x10007fff8000 <= b -> b + 8192 <= ATOP ->
  (t + 4096 <= b \/ b + 8192 <= t) -> (t + 4096 <= lst \/ lst + 8192 <= t \/ lst = 0) -> (b + 8192 <= lst \/ lst + 8192 <= b) ->
  (hm + 24 <= b \/ b + 8192 <= hm) -> (hm + 24 <= lst \/ lst + 8192 <= hm) ->
  rng RNG b 8192 ->
  ek_seps ek L hm lst ->
  (* [comment removed for export] *)
  dk_pre ek g RNG t lst hm (qb + ek_delta ek n) m -> dk_seps g L hm ->
  (* [comment removed for export] *)
  ADEPOT DI L m ->
  sclr (al_nodes L) 1048576 -> al_nodes L + 1048576 <= ATOP -> sclr (al_store L) 8388608 -> al_store L + 8388608 <= ATOP ->
  (t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) -> (t + 4096 <= al_store L \/ al_store L + 8388608 <= t) ->
  bv_unsigned sp < 2^47 ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 -> rng RNG hm 24 -> rng RNG (shad (hm + 16)) (shlen (rup n 8)) ->
  AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L -> iclr t 4096 ->      (* [comment removed for export] *)
  evtF asegs RNG (free_fast_post DI L ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n nb fst0 lst qb b1 actx lo m)
    (MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + -2272)) gp tp t0 t1 t2 (Z_to_bv 64 (t + 2128)) (Z_to_bv 64 (t + 208))
             (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 hm) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 n) (Z_to_bv 64 Q_CACHE)
             s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x382f8) fc None m (seg_rom asegs)).
Section Zd2.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 0).
Variable full : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 1).
Variable g : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 2).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 3).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 4).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 5).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 6).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 7).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 8).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 9).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 10).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 11).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 12).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 13).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 14).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 15).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 16).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 17).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 18).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 19).
Variable ra0 : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 20).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 21).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 22).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 23).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 24).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 25).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 26).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 27).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 28).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 29).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 30).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 31).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 32).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 33).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 34).
Variable F : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 35).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 36).
Variable m : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 37).
Variable t : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 38).
Variable hm : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 39).
Variable n : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 40).
Variable b1 : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 41).
Variable actx : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 42).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 43).
Variable nb : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 44).
Variable fst0 : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 45).
Variable lst : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 46).
Variable qb : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 47).
Variable nx : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 48).
Variable bsz : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 49).
Variable cnt : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 50).
Variable spacebeg : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 51).
Variable id : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 52).
Variable b : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 53).
Variable maxc : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 54).
Variable csz : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 55).
Variable stj : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 56).
Variable idxw : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 57).
Variable sj : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 58).
Variable tb : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 59).
Variable chunks : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 60).
Variable hs : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 61).
Variable junk2 : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 62).
Variable j0 : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 63).
Variable trt : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 64).
Let sp1 := Z_to_bv 64 (bv_unsigned sp + -2128).
#[using="sp1"] Lemma free_from_refill_spec__body : ltac:(let T := type of (fun (h : free_from_refill_spec__stmt) => h L full g RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m t hm n b1 actx lo nb fst0 lst qb nx bsz cnt spacebeg id b maxc csz stj idxw sj tb chunks hs junk2 j0 trt) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (full, (g, (RNG, (ra, (sp, (gp, (tp, (s0, (s1, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (ra0, (t0, (t1, (t2, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (t3, (t4, (t5, (t6, (F, (fc, (m, (t, (hm, (n, (b1, (actx, (lo, (nb, (fst0, (lst, (qb, (nx, (bsz, (cnt, (spacebeg, (id, (b, (maxc, (csz, (stj, (idxw, (sj, (tb, (chunks, (hs, (junk2, (j0, trt))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) as _.
 cbv zeta.
  intros ST CEIL LO MI SS TB LTB FRS FRP FRE QK HD FC IDR N AL HLO TCH HHI HCE SH QC NB QB QBN FST LST T0 T1 TAL DHT STATS LSJ UW FL IAS IAM
         FULL SB CR CH LCH CNT NTH IXS STS HBE BJ SBP B0 BL1 DTB DTL DBL DHB DHL RB ES DK DS DEP N0 N1 R0 R1 DTN DTS SP47
         RIMG RTLS RSTK RT RH RSH NI SI TI. band_lin.   (* [comment removed for export] *)
  band_int TI. (pose proof (ablk_lin _ _ HLO) as ndP__; nd_pre ndP__ 4%nat; intros HL1 HL2 HL3 HL4; nd_post). unfold AIMG_HI in HL1. band_int HLO. band_int T0. band_int N0. band_int R0.   (* [comment removed for export] *)
  assert (RUP : n <= rup n 8 <= n + 7 /\ rup n 8 mod 8 = 0) by (clear -N; unfold rup; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
  assert (SHB : 2148238848 <= shad (hm + 16) /\ shad (hm + 16) + shlen (rup n 8) <= 0x10007fff8000 /\ 0 < shlen (rup n 8)).
  { clear -N HLO HL1 HHI HCE. unfold shad, shlen, ASHOFF, rup in *. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold Q_MAX in *. Z.div_mod_to_equations. lia. }
  (pose proof (dk_pre_pure _ g RNG L t lst hm (qb + (n + 8192)) m DK DS TI ltac:(unfold AIMG_HI; lia) NI SI
                DHL DTL ltac:(cbn [ek_seps] in ES; destruct full; [destruct ES as (_ & _ & _ & S4); destruct FULL as (_ & _ & _ & _ & L0 & _); exact (proj1 (proj2 (S4 eq_refl))) | destruct FULL as [_ ->]; unfold AIMG_HI in *; lia])
                ltac:(cbn [ek_seps] in ES; destruct full; [destruct ES as (_ & _ & _ & S4); exact (proj2 (proj2 (S4 eq_refl))) | destruct FULL as [_ ->]; unfold AIMG_HI in *; lia])
                ltac:(destruct full; [destruct FULL as (_ & _ & _ & _ & L0 & _) | destruct FULL as [_ ->]]; unfold AIMG_HI in *; lia)
                ltac:(destruct full; [destruct FULL as (_ & _ & _ & _ & L0 & L1 & _) | destruct FULL as [_ ->]]; unfold AIMG_HI in *; atop_facts; lia)
                ltac:(destruct full; [destruct FULL as (_ & _ & _ & _ & L0 & _); right | destruct FULL as [_ ->]; left]; unfold AIMG_HI in *; lia)) as ndP__; nd_pre ndP__ 7%nat; intros DF1 DF2 DF3 DF4 DG0 DG1 DG2; nd_post).
  cbn [ek_seps] in ES. (nd_pre ES 4%nat; intros SB1 SB2 SB3 SL; nd_post).
  assert (PL2 : lst = 0 \/ 0x10007fff8000 <= lst) by (destruct full; [(nd_pre FULL 6%nat; intros _ _ _ _ L0 _; nd_post); right; exact L0 | destruct FULL as [_ E0]; left; exact E0]).
  assert (PLB : lst + 8192 <= ATOP) by (destruct full; [(nd_pre FULL 7%nat; intros _ _ _ _ _ L1 _; nd_post); exact L1 | destruct FULL as [_ E0]; rewrite E0; atop_facts; lia]).
  (pose proof (qsz_int lst ltac:(clear -PL2; lia) ltac:(clear -PLB; atop_facts; lia)) as ndP__; nd_pre ndP__ 5%nat; intros zq QZ0 QZ1 QZ2 QZ3; nd_post).   (* [comment removed for export] *)
  unfold AIMG_HI, AFREE_SYM, AFREE_PC in *.
  word_range sp SPR.
  box DHT. box DTN. box DTS. box DTB. box DTL. box DBL. box DHB. box DHL. box SB1. box SB2. box SB3. box DF1. box DF2. box DF3. box DF4. box DG2. box PL2.
  (* [comment removed for export] *)
  chg (Z_to_bv 64 (bv_unsigned sp + -2128)) sp1.
  assert (Hsp : bv_unsigned sp1 = bv_unsigned sp + -2128) by (subst sp1; apply unsigned_lit; lia).
  replace (bv_unsigned sp + -2272) with (bv_unsigned sp1 + -144) in * by lia.
  replace (bv_unsigned sp + -2208) with (bv_unsigned sp1 + -80) in * by lia.
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (put_from_refill_spec full g t hm lst b RNG (Z_to_bv 64 0x5632c) sp1 gp tp sp (Z_to_bv 64 (hm + 16)) (Z_to_bv 64 (t + 208)) sp1
              (Z_to_bv 64 0x562bc) (Z_to_bv 64 1) sp1 (Z_to_bv 64 (bv_unsigned sp + -81)) s6 s7 s8 s9 s10 s11
              ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m n nb fst0 qb b1 actx lo nx bsz cnt spacebeg maxc csz stj idxw chunks hs j0).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact ST | exact IAS]
         | |- mem_inv _ _ => exact MI
         | |- if _ then _ else _ => exact FULL
         | |- dk_pre _ _ _ _ _ _ _ _ => exact DK
         | |- @eq word _ _ => reflexivity
         | |- @eq Z _ _ => first [exact HBE | lia]
         | |- ex _ => exact BJ
         | |- _ \/ _ => first [ub DHT; ylia | ub DTB; ylia | ub DTL; ylia | ub DBL; ylia | ub DHB; ylia | ub DHL; ylia]
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD
         | |- rw_cells _ _ (shad _) _ => exact SH
         | |- rw_cells _ _ (_ + 80) _ => exact QC
         | |- rw_cells _ _ (_ + 2128) _ => exact CR
         | |- rw_cells _ _ (_ + 2784) _ => exact STS
         | |- rw_cells _ _ (_ + -80) _ => exact FRP
         | |- iclr _ _ => exact TI
         | |- rw_cells _ _ (_ + -144) _ => exact FRE
         | |- u32arr _ _ _ _ => exact CH
         | |- nth_error _ _ = _ => exact NTH
         end.
    all: try eassumption. all: try (unfold AIMG_HI, Q_MAX in *; lia).
    all: match goal with |- ?G => idtac "REMQ" G end. }
  cbv beta. intros ms2 PP. unfold put_tail_post in PP.
  (nd_pre PP 17%nat; intros t0b t1b t2b a0b a1b a2b a3b a4b a5b a6b a7b t3b t4b t5b t6b m2 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 9%nat; intros MUp WMp MIp STp SH2 HD2 QC2 EKP DKP; nd_post).
  replace (ret_pc (Z_to_bv 64 353068)) with (Z_to_bv 64 353068) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  (* [comment removed for export] *)
  cbn [ek_b] in MUp.
  xport FC MUp WMp ltac:(ub DHT; ub DHB; ub DHL; ub DF1; ylia).
  xport STATS MUp WMp ltac:(rewrite LSJ; ub DTB; ub DTL; ub DF2; ylia).
  xport UW MUp WMp ltac:(ub DTB; ub DTL; ub DF2; ylia).
  xport FL MUp WMp ltac:(ub DG2; ub PL2; ylia). xport IAS MUp WMp ltac:(ub DG2; ub PL2; ylia).
  xport SS MUp WMp ltac:(lia). xport TB MUp WMp ltac:(rewrite LTB; lia). xport FRS MUp WMp ltac:(lia).
  assert (IAM2 : forall j, 0 <= j < 32768 -> bytes_at asegs m2 (0xaf808 + 8 * j) (le8 (Z_to_bv 64 0))).
  { (intros j Hj; eapply bytes_at_agree; [exact (IAM j Hj)|];
    intros i Hi; apply MUp; cbn [outside]; rewrite length_le8 in Hi; rewrite wa_unsigned by lia; ub DG2; ub PL2; ylia). }
  clear IAM.
  assert (DEP2 : ADEPOT DI L m2).
  { eapply (adi_frame DI); [exact DEP | exact MUp | exact WMp |].
    ((first [ apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [ lia |lia | ub DTN; ub DTS; ylia | ub SB2; ub SB3; ylia | ub DF3; ub DF4; ub DG2; ylia
            | destruct full; [(nd_pre (SL eq_refl) 3%nat; intros _ S6 S7; nd_post); lia | destruct FULL as [_ LST0]; lia] ] | first [ apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [ lia |lia | ub DTN; ub DTS; ylia | ub SB2; ub SB3; ylia | ub DF3; ub DF4; ub DG2; ylia
            | destruct full; [(nd_pre (SL eq_refl) 3%nat; intros _ S6 S7; nd_post); lia | destruct FULL as [_ LST0]; lia] ] | first [ apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [ ub DTN; ub DTS; ylia |lia | ub DTN; ub DTS; ylia | ub SB2; ub SB3; ylia | ub DF3; ub DF4; ub DG2; ylia
            | destruct full; [(nd_pre (SL eq_refl) 3%nat; intros _ S6 S7; nd_post); lia | destruct FULL as [_ LST0]; lia] ] | first [ apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [ ub DTN; ub DTS; ylia |lia | ub DTN; ub DTS; ylia | ub SB2; ub SB3; ylia | ub DF3; ub DF4; ub DG2; ylia
            | destruct full; [(nd_pre (SL eq_refl) 3%nat; intros _ S6 S7; nd_post); lia | destruct FULL as [_ LST0]; lia] ] | first [ apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [ ub DTN; ub DTS; ylia |lia | ub DTN; ub DTS; ylia | ub SB2; ub SB3; ylia | ub DF3; ub DF4; ub DG2; ylia
            | destruct full; [(nd_pre (SL eq_refl) 3%nat; intros _ S6 S7; nd_post); lia | destruct FULL as [_ LST0]; lia] ] | first [ apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [ destruct full; [(nd_pre (SL eq_refl) 3%nat; intros _ S6 S7; nd_post); lia | destruct FULL as [_ LST0]; lia] |lia | ub DTN; ub DTS; ylia | ub SB2; ub SB3; ylia | ub DF3; ub DF4; ub DG2; ylia
            | destruct full; [(nd_pre (SL eq_refl) 3%nat; intros _ S6 S7; nd_post); lia | destruct FULL as [_ LST0]; lia] ] | first [ apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [ ub SB2; ub SB3; ylia |lia | ub DTN; ub DTS; ylia | ub SB2; ub SB3; ylia | ub DF3; ub DF4; ub DG2; ylia
            | destruct full; [(nd_pre (SL eq_refl) 3%nat; intros _ S6 S7; nd_post); lia | destruct FULL as [_ LST0]; lia] ] | first [ apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [ lia |lia | ub DTN; ub DTS; ylia | ub SB2; ub SB3; ylia | ub DF3; ub DF4; ub DG2; ylia
            | destruct full; [(nd_pre (SL eq_refl) 3%nat; intros _ S6 S7; nd_post); lia | destruct FULL as [_ LST0]; lia] ] | first [ apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [ lia |lia | ub DTN; ub DTS; ylia | ub SB2; ub SB3; ylia | ub DF3; ub DF4; ub DG2; ylia
            | destruct full; [(nd_pre (SL eq_refl) 3%nat; intros _ S6 S7; nd_post); lia | destruct FULL as [_ LST0]; lia] ] | first [ apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [ ub DF3; ub DF4; ub DG2; ylia |lia | ub DTN; ub DTS; ylia | ub SB2; ub SB3; ylia | ub DF3; ub DF4; ub DG2; ylia
            | destruct full; [(nd_pre (SL eq_refl) 3%nat; intros _ S6 S7; nd_post); lia | destruct FULL as [_ LST0]; lia] ] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub SB2; ub SB3; ylia | ub DF3; ub DF4; ub DG2; ylia
            | destruct full; [(nd_pre (SL eq_refl) 3%nat; intros _ S6 S7; nd_post); lia | destruct FULL as [_ LST0]; lia] ] |])] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub SB2; ub SB3; ylia | ub DF3; ub DF4; ub DG2; ylia
            | destruct full; [(nd_pre (SL eq_refl) 3%nat; intros _ S6 S7; nd_post); lia | destruct FULL as [_ LST0]; lia] ] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub SB2; ub SB3; ylia | ub DF3; ub DF4; ub DG2; ylia
            | destruct full; [(nd_pre (SL eq_refl) 3%nat; intros _ S6 S7; nd_post); lia | destruct FULL as [_ LST0]; lia] ] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub SB2; ub SB3; ylia | ub DF3; ub DF4; ub DG2; ylia
            | destruct full; [(nd_pre (SL eq_refl) 3%nat; intros _ S6 S7; nd_post); lia | destruct FULL as [_ LST0]; lia] ] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub SB2; ub SB3; ylia | ub DF3; ub DF4; ub DG2; ylia
            | destruct full; [(nd_pre (SL eq_refl) 3%nat; intros _ S6 S7; nd_post); lia | destruct FULL as [_ LST0]; lia] ] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub SB2; ub SB3; ylia | ub DF3; ub DF4; ub DG2; ylia
            | destruct full; [(nd_pre (SL eq_refl) 3%nat; intros _ S6 S7; nd_post); lia | destruct FULL as [_ LST0]; lia] ] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub SB2; ub SB3; ylia | ub DF3; ub DF4; ub DG2; ylia
            | destruct full; [(nd_pre (SL eq_refl) 3%nat; intros _ S6 S7; nd_post); lia | destruct FULL as [_ LST0]; lia] ] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub SB2; ub SB3; ylia | ub DF3; ub DF4; ub DG2; ylia
            | destruct full; [(nd_pre (SL eq_refl) 3%nat; intros _ S6 S7; nd_post); lia | destruct FULL as [_ LST0]; lia] ] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub SB2; ub SB3; ylia | ub DF3; ub DF4; ub DG2; ylia
            | destruct full; [(nd_pre (SL eq_refl) 3%nat; intros _ S6 S7; nd_post); lia | destruct FULL as [_ LST0]; lia] ] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub SB2; ub SB3; ylia | ub DF3; ub DF4; ub DG2; ylia
            | destruct full; [(nd_pre (SL eq_refl) 3%nat; intros _ S6 S7; nd_post); lia | destruct FULL as [_ LST0]; lia] ] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub SB2; ub SB3; ylia | ub DF3; ub DF4; ub DG2; ylia
            | destruct full; [(nd_pre (SL eq_refl) 3%nat; intros _ S6 S7; nd_post); lia | destruct FULL as [_ LST0]; lia] ] |]) ]); apply Forall_nil). }
  clear DEP.
  (* [comment removed for export] *)
  subst sp1. rewrite ?unsigned_lit in STp by lia. rewrite ?unsigned_lit in MUp by lia.
  apply rw_cells_of_u64arr in TB. rewrite LTB in TB.
  eapply evtF_mono.
  { (eapply (ficptD_spec RNG sp gp tp); [exact STp | atop_facts; lia | lia | exact MIp
      | eexists; split; [exact SS | reflexivity]
      | eexists; split; [replace (bv_unsigned sp + -2112) with (bv_unsigned sp + -2128 + 16) by lia; exact TB | reflexivity]
      | exact FRS | exact RIMG | exact RTLS | solve_rng ]). }
  cbv beta. intros ms3 [-> ST3].
  (* [comment removed for export] *)
  assert (MU : munch (free_W L sp t hm n lst (EkNew full nx bsz cnt maxc csz stj idxw chunks spacebeg b hs) g) m m2).
  { eapply munch_weaken; [| exact MUp]. cbn [ek_b]. solve_sub_fp sp. }
  unfold free_fast_post. exists id. do 15 eexists. exists m2, sj.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WMp|]. split; [exact MIp|]. split; [exact ST3|]. split; [exact IDR|].
  split; [exact HD2|]. split; [exact FC|]. split; [exact SH2|]. split; [exact QC2|]. split; [exact EKP|]. split; [exact DKP|].
  split; [exact STATS|]. split; [exact LSJ|]. split; [exact UW|]. split; [exact FL|]. split; [exact IAS|]. split; [exact IAM2|].
  exact DEP2.
  Unshelve. all: try exact ST; try exact STp.
Qed.
End Zd2.
#[using="Type"] Lemma free_from_refill_spec : ltac:(let t := eval cbv delta [free_from_refill_spec__stmt] in free_from_refill_spec__stmt in exact t).
Proof. exact free_from_refill_spec__body. Qed.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_afree_iseg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_front.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tail.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_aenqueueR.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tailR__A3W.F_afree_tailR.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_icpt.TwB.
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
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section WithDepot.
Variable DI : ADepotIface.

Notation free_W L sp t hm n lst ek g :=
  ([(bv_unsigned sp - 4096, bv_unsigned sp); (0xafc00, 0xafc00 + 0x81030); (0x13e488, 0x13e488 + 4);
    (t + 3168, t + 3169); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608);
    (shad (hm + 16), shad (hm + 16) + shlen (rup n 8)); (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792);
    (lst, lst + qsz lst); (ek_b ek lst, ek_b ek lst + 8192);
    (0xab708, 0xab708 + 4); (0xab710, 0xab710 + 32); (dk_glst g lst, dk_glst g lst + 8)]%Z) (only parsing).
Notation toref_W L sp t hm n :=
  ([(bv_unsigned sp - 4096, bv_unsigned sp); (0xafc00, 0xafc00 + 0x81030); (0x13e488, 0x13e488 + 4);
    (t + 3168, t + 3169); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608);
    (shad (hm + 16), shad (hm + 16) + shlen (rup n 8))]%Z) (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition free_to_refill_post (L : alayout) (full : bool)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t hm n b1 actx lo lst nx bsz : Z) (hs : list word) (trt : list Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (id : Z) (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) m' (sj' tb' : list word) (junk2 j0 : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x38360) (Z_to_bv 64 (bv_unsigned sp + -2272)) gp tp t0 t1 t2
                  (Z_to_bv 64 (t + 2128)) (Z_to_bv 64 (t + 208))
                  (Z_to_bv 64 (t + 208)) (Z_to_bv 64 (t + 2128)) (Z_to_bv 64 0xab398) (Z_to_bv 64 K_BATCH_CLASS) a4 a5 a6 a7
                  (Z_to_bv 64 hm) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 n) (Z_to_bv 64 Q_CACHE)
                  s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x38b40) fc None m' (seg_rom asegs)
    /\ munch (toref_W L sp t hm n) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -2272)
    /\ 0 < id < 2^31
    /\ rw_cells asegs m' hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)]
    /\ rw_cells asegs m' (hm + 16) [C8 (Z_to_bv 64 id)]
    /\ rw_cells asegs m' (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) (repeat (Z_to_bv 8 253) (Z.to_nat (shlen (rup n 8))))]
    /\ u64arr asegs m' (t + 2800) sj' /\ length sj' = 46%nat
    /\ rw_cells asegs m' (t + 3168) [C1 (Z_to_bv 8 0)]
    /\ rw_cells asegs m' 0x13e488 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ stk asegs m' 0xafc00 (0xafc00 + 0x81030)
    /\ (forall j, 0 <= j < 32768 -> bytes_at asegs m' (0xafc08 + 8 * j) (le8 (Z_to_bv 64 0)))
    (* [comment removed for export] *)
    /\ rw_cells asegs m' (bv_unsigned sp + -2128) [C8 (Z_to_bv 64 (bv_unsigned sp + -2128 + 16)); C4 (Z_to_bv 64 (1 + Z.of_nat (length trt))); C4 (Z_to_bv 64 0)]
    /\ u64arr asegs m' (bv_unsigned sp + -2128 + 16) tb' /\ length tb' = 255%nat
    /\ rw_cells asegs m' (bv_unsigned sp + -72) [C8 sp; CB 8 junk2; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' (bv_unsigned sp + -2208)
         [C8 (Z_to_bv 64 (t + 208)); C8 (Z_to_bv 64 (bv_unsigned sp + -2128)); C8 s6; C8 (Z_to_bv 64 (bv_unsigned sp + -81));
          C8 (Z_to_bv 64 (bv_unsigned sp + -2128)); C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 0x56324); C8 (Z_to_bv 64 (hm + 16)); C8 sp; C8 (Z_to_bv 64 0x56394)]
    /\ rw_cells asegs m' (bv_unsigned sp + -2272)
         [CB 8 j0; C8 (Z_to_bv 64 hm); C8 (Z_to_bv 64 (t + 208)); C8 (Z_to_bv 64 (bv_unsigned sp + -2128)); C8 (Z_to_bv 64 n);
          C8 (Z_to_bv 64 (t + 80)); C8 (Z_to_bv 64 0xab670); C8 (Z_to_bv 64 0x38200)]
    /\ (if full then rw_cells asegs m' lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)] /\ u64arr asegs m' (lst + 24) hs else True)
    /\ ADEPOT DI L m'.

Definition free_to_refill_spec__stmt : Prop := forall (L : alayout) (ia full : bool) RNG
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem)
    (t ctx hm n b1 actx lo top bot nb fst0 lst qb nx bsz : Z) (uw maxc csz : word) (sj hs : list word) (sjunk : list byte) (trt : list Z),
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
  (if full then 0 < nb /\ rw_cells asegs m lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)]
             /\ 0x10007fff8000 <= lst /\ lst + 8192 <= ATOP
             /\ u64arr asegs m (lst + 24) hs /\ length hs = 1021%nat /\ rng RNG lst 8192
   else nb = 0 /\ lst = 0) ->
  rw_cells asegs m (t + 2128) [C4 (Z_to_bv 64 0); C4 maxc; C8 csz] ->
  (t + 4096 <= lst \/ lst + 8192 <= t \/ lst = 0) -> (hm + 24 <= lst \/ lst + 8192 <= hm) ->
  (al_nodes L + 1048576 <= lst \/ lst + 8192 <= al_nodes L) -> (al_store L + 8388608 <= lst \/ lst + 8192 <= al_store L) ->
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
  evtF asegs RNG (free_to_refill_post L full ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n b1 actx lo lst nx bsz hs trt m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 0).
Variable ia : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 1).
Variable full : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 2).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 3).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 4).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 5).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 6).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 7).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 8).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 9).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 10).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 11).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 12).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 13).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 14).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 15).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 16).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 17).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 18).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 19).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 20).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 21).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 22).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 23).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 24).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 25).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 26).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 27).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 28).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 29).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 30).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 31).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 32).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 33).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 34).
Variable F : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 35).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 36).
Variable m : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 37).
Variable t : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 38).
Variable ctx : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 39).
Variable hm : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 40).
Variable n : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 41).
Variable b1 : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 42).
Variable actx : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 43).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 44).
Variable top : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 45).
Variable bot : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 46).
Variable nb : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 47).
Variable fst0 : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 48).
Variable lst : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 49).
Variable qb : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 50).
Variable nx : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 51).
Variable bsz : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 52).
Variable uw : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 53).
Variable maxc : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 54).
Variable csz : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 55).
Variable sj : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 56).
Variable hs : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 57).
Variable sjunk : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 58).
Variable trt : ltac2:(SecDietF.SzSecF.ty 'free_to_refill_spec__stmt 59).
#[using="Type"] Lemma free_to_refill_spec__body : ltac:(let T := type of (fun (h : free_to_refill_spec__stmt) => h L ia full RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m t ctx hm n b1 actx lo top bot nb fst0 lst qb nx bsz uw maxc csz sj hs sjunk trt) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (ia, (full, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (t, (ctx, (hm, (n, (b1, (actx, (lo, (top, (bot, (nb, (fst0, (lst, (qb, (nx, (bsz, (uw, (maxc, (csz, (sj, (hs, (sjunk, trt)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) as _.

  intros ST CEIL LO MI TP Ha0 SP16 AC PC MCS CF34 GPG PGC HK QK GF FLG FL IAS IAM CT8 TT0 SW UW STATS LSJ QC NB QB QBN FST LST
         CX0 C0 C1 T0 T1 TAL CT2 HD HUW B1 B13 N AL HLO TCH HHI HCE SH DHT DHC FULL CR0 DTL DHL DNL DSL DEP N0 N1 R0 R1 DHN DHS DTN DTS DCN DCS XTNO XTST
         UNW S0NE TRU B0 BB BOTOP TOP RA4 RANE RIMG RTLS RSTK RCTX RT RNO RST RH RSH CI NI SI TI. band_lin.   (* [comment removed for export] *)
  band_int TI. (pose proof (ablk_lin _ _ HLO) as ndP__; nd_pre ndP__ 4%nat; intros HL1 HL2 HL3 HL4; nd_post). unfold AIMG_HI in HL1. band_int HLO. band_int C0. band_int T0. band_int N0. band_int R0.   (* [comment removed for export] *)
  pose proof (afree_unw_length _ _ _ _ _ _ _ _ UNW) as LTRT.
  pose proof (afree_unw_sp47 _ _ _ _ _ _ _ _ UNW ltac:(clear -TOP; lia)) as SP47.
  pose proof PC as PC'. destruct PC' as (GOT6 & _).
  assert (RUP : n <= rup n 8 <= n + 7 /\ rup n 8 mod 8 = 0) by (clear -N; unfold rup; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
  assert (SHB : 2148239360 <= shad (hm + 16) /\ shad (hm + 16) + shlen (rup n 8) <= 0x10007fff8000 /\ 0 < shlen (rup n 8)).
  { clear -N HLO HL1 HHI HCE. unfold shad, shlen, ASHOFF, rup in *. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold Q_MAX in *. Z.div_mod_to_equations. lia. }
  unfold AIMG_HI, AFREE_SYM, AFREE_PC in *.
  word_range sp SPR.
  box DHT. box DHC. box DHN. box DHS. box DTN. box DTS. box DCN. box DCS. box CT2. box DTL. box DHL. box DNL. box DSL.
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
  xport CR0 MUf WMf ltac:(ub DHT; ub DTN; ub DTS; ylia).
  assert (PC1 : poison_cells m1).
  { eapply poison_cells_frame2; [exact PC | exact MUf | exact WMf |].
    repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
  assert (FULL1 : if full then 0 < nb /\ rw_cells asegs m1 lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)]
             /\ 0x10007fff8000 <= lst /\ lst + 8192 <= ATOP
             /\ u64arr asegs m1 (lst + 24) hs /\ length hs = 1021%nat /\ rng RNG lst 8192
           else nb = 0 /\ lst = 0).
  { destruct full; [| exact FULL]. (nd_pre FULL 7%nat; intros NB1 LB L0 L1 LA0 LEN0 RL; nd_post).
    xport LB MUf WMf ltac:(ub DTL; ub DHL; ub DNL; ub DSL; ylia). xport LA0 MUf WMf ltac:(rewrite LEN0; ub DTL; ub DHL; ub DNL; ub DSL; ylia).
    split; [exact NB1|]. split; [exact LB|]. split; [exact L0|]. split; [exact L1|]. split; [exact LA0|]. split; [exact LEN0| exact RL]. }
  clear FULL PC.
  (* [comment removed for export] *)
  name_sp sp (-2128).
  eapply evtF_cut.
  { eapply (put_to_refill_spec full t hm lst RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 n nb fst0 qb b1 actx lo nx bsz maxc csz hs sjunk).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => rewrite Hsp; exact STf
         | |- mem_inv _ _ => exact MIf
         | |- poison_cells _ => exact PC1
         | |- @eq word _ _ => rewrite ?Esp; first [reflexivity | apply Z_to_bv_eqm; rewrite ?unsigned_lit by lia; lia]
         | |- if _ then _ else _ => exact FULL1
         | |- _ \/ _ => first [ub DHT; ylia | ub DTL; ylia | ub DHL; ylia]
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD1
         | |- rw_cells _ _ (shad _) _ => exact SH
         | |- rw_cells _ _ (_ + 80) _ => exact QC
         | |- rw_cells _ _ (_ + 2128) _ => exact CR0
         | |- iclr _ _ => exact TI
         end.
    all: try eassumption. all: try (unfold AIMG_HI, Q_MAX in *; lia).
    all: match goal with |- ?G => idtac "REMP" G end. }
  cbv beta. intros ms2 PP. unfold put_to_refill_post in PP.
  (nd_pre PP 14%nat; intros t0b t1b t2b a4b a5b a6b a7b t3b t4b t5b t6b m2 j0 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 8%nat; intros MUp WMp MIp STp SH2 FRP FRE LBS; nd_post).
  unname_sp. rewrite ?unsigned_lit in MUp by lia. rewrite ?unsigned_lit in STp by lia.
  rewrite ?unsigned_lit in FRP by lia. rewrite ?unsigned_lit in FRE by lia.
  replace (bv_unsigned sp + -2128 + -80) with (bv_unsigned sp + -2208) in * by lia.
  replace (bv_unsigned sp + -2128 + -144) with (bv_unsigned sp + -2272) in * by lia.
  (* [comment removed for export] *)
  xport HD1 MUp WMp ltac:(lia). xport FC1 MUp WMp ltac:(lia).
  xport STATS1 MUp WMp ltac:(rewrite LSJ1; lia).
  xport UW1 MUp WMp ltac:(lia).
  xport FL1 MUp WMp ltac:(lia). xport IAS1 MUp WMp ltac:(lia).
  xport SS1 MUp WMp ltac:(lia). xport TB1 MUp WMp ltac:(rewrite LTB1; lia). xport FRS1 MUp WMp ltac:(lia).
  assert (IAM2 : forall j, 0 <= j < 32768 -> bytes_at asegs m2 (0xafc08 + 8 * j) (le8 (Z_to_bv 64 0))).
  { (intros j Hj; eapply bytes_at_agree; [exact (IAM1 j Hj)|];
    intros i Hi; apply MUp; cbn [outside]; rewrite length_le8 in Hi; rewrite wa_unsigned by lia; lia). }
  clear IAM1.
  assert (DEP2 : ADEPOT DI L m2).
  { eapply (adi_frame DI); [exact DEP1 | exact MUp | exact WMp |].
    (repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq; first [lia | ub DTN; ub DTS; ylia] |]); apply Forall_nil). }
  clear DEP1.
  (* [comment removed for export] *)
  assert (MU : munch (toref_W L sp t hm n) m m2).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUp]].
    eapply munch_weaken; [| exact MUf].
    all: solve_sub_fp sp. }
  assert (WM : wmono asegs m m2) by (eapply wmono_trans; [exact WMf| exact WMp]).
  apply evtF_done. unfold free_to_refill_post. exists id. do 11 eexists. exists m2, sj1, tb1, junk2, j0.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MIp|]. split; [exact STp|]. split; [exact IDR|].
  split; [exact HD1|]. split; [exact FC1|]. split; [exact SH2|].
  split; [exact STATS1|]. split; [exact LSJ1|]. split; [exact UW1|]. split; [exact FL1|]. split; [exact IAS1|]. split; [exact IAM2|].
  split; [exact SS1|]. split; [exact TB1|]. split; [exact LTB1|]. split; [exact FRS1|]. split; [exact FRP|]. split; [exact FRE|].
  split; [exact LBS|]. exact DEP2.
  Unshelve. all: try exact STf; try exact STp.
Qed.
End Zd1.
#[using="Type"] Lemma free_to_refill_spec : ltac:(let t := eval cbv delta [free_to_refill_spec__stmt] in free_to_refill_spec__stmt in exact t).
Proof. exact free_to_refill_spec__body. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition free_from_refill_spec__stmt : Prop := forall (L : alayout) (full : bool) (g : gqd) RNG
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : amem)
    (t hm n b1 actx lo nb fst0 lst qb nx bsz cnt spacebeg id b : Z) (maxc csz stj idxw : word) (sj tb chunks hs : list word)
    (junk2 j0 : list byte) (trt : list Z),
  let ek := EkNew full nx bsz cnt maxc csz stj idxw chunks spacebeg b hs in
  stk asegs m lo (bv_unsigned sp + -2272) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
  mem_inv asegs m ->
  (* [comment removed for export] *)
  rw_cells asegs m (bv_unsigned sp + -2128) [C8 (Z_to_bv 64 (bv_unsigned sp + -2128 + 16)); C4 (Z_to_bv 64 (1 + Z.of_nat (length trt))); C4 (Z_to_bv 64 0)] ->
  u64arr asegs m (bv_unsigned sp + -2128 + 16) tb -> length tb = 255%nat ->
  rw_cells asegs m (bv_unsigned sp + -72) [C8 sp; CB 8 junk2; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m (bv_unsigned sp + -2208)
     [C8 (Z_to_bv 64 (t + 208)); C8 (Z_to_bv 64 (bv_unsigned sp + -2128)); C8 s6; C8 (Z_to_bv 64 (bv_unsigned sp + -81));
      C8 (Z_to_bv 64 (bv_unsigned sp + -2128)); C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 0x56324); C8 (Z_to_bv 64 (hm + 16)); C8 sp; C8 (Z_to_bv 64 0x56394)] ->
  rw_cells asegs m (bv_unsigned sp + -2272)
     [CB 8 j0; C8 (Z_to_bv 64 hm); C8 (Z_to_bv 64 (t + 208)); C8 (Z_to_bv 64 (bv_unsigned sp + -2128)); C8 (Z_to_bv 64 n);
      C8 (Z_to_bv 64 (t + 80)); C8 (Z_to_bv 64 0xab670); C8 (Z_to_bv 64 0x38200)] ->
  (* [comment removed for export] *)
  rw_cells asegs m 0xab6b0 [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->
  (* [comment removed for export] *)
  rw_cells asegs m hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  rw_cells asegs m (hm + 16) [C8 (Z_to_bv 64 id)] -> 0 < id < 2^31 ->
  1 <= n <= Q_MAX -> hm mod 16 = 0 -> ablk hm (hm + 16 + rup n 8) -> tclr hm 24 -> hm + 16 + rup n 8 <= ATOP -> hm + 24 <= ATOP ->
  rw_cells asegs m (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) (repeat (Z_to_bv 8 253) (Z.to_nat (shlen (rup n 8))))] ->
  (* [comment removed for export] *)
  rw_cells asegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= qb -> qb + n + 8192 < 2^62 -> 0 <= fst0 < 2^64 -> 0 <= lst < 2^64 ->
  sclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> t mod 4096 = 0 -> (hm + 24 <= t \/ t + 4096 <= hm) ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat -> rw_cells asegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m 0x13e488 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  stk asegs m 0xafc00 (0xafc00 + 0x81030) ->
  (forall j, 0 <= j < 32768 -> bytes_at asegs m (0xafc08 + 8 * j) (le8 (Z_to_bv 64 0))) ->
  (* [comment removed for export] *)
  (if full then 0 < nb /\ rw_cells asegs m lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)]
             /\ 0 <= nx < 2^64 /\ 0 <= bsz < 2^64 /\ 0x10007fff8000 <= lst /\ lst + 8192 <= ATOP
             /\ u64arr asegs m (lst + 24) hs /\ length hs = 1021%nat
             /\ rng RNG lst 8192
   else nb = 0 /\ lst = 0) ->
  rw_cells asegs m 0xab3b8 [C8 (Z_to_bv 64 spacebeg)] ->
  rw_cells asegs m (t + 2128) [C4 (Z_to_bv 64 cnt); C4 maxc; C8 csz] ->
  u32arr asegs m (t + 2128 + 16) chunks -> length chunks = 16%nat ->
  0 < cnt <= 16 -> nth_error chunks (Z.to_nat (cnt - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
  rw_cells asegs m (t + 2784) [C8 stj] ->
  b = spacebeg + 24 * 2^32 + 16 * bv_unsigned idxw ->
  (exists bs, rw_cells asegs m b [CB (Z.to_nat 8192) bs]) ->
  0 < spacebeg -> 0x10007fff8000 <= b -> b + 8192 <= ATOP ->
  (t + 4096 <= b \/ b + 8192 <= t) -> (t + 4096 <= lst \/ lst + 8192 <= t \/ lst = 0) -> (b + 8192 <= lst \/ lst + 8192 <= b) ->
  (hm + 24 <= b \/ b + 8192 <= hm) -> (hm + 24 <= lst \/ lst + 8192 <= hm) ->
  rng RNG b 8192 ->
  ek_seps ek L hm lst ->
  (* [comment removed for export] *)
  dk_pre ek g RNG t lst hm (qb + ek_delta ek n) m -> dk_seps g L hm ->
  (* [comment removed for export] *)
  ADEPOT DI L m ->
  sclr (al_nodes L) 1048576 -> al_nodes L + 1048576 <= ATOP -> sclr (al_store L) 8388608 -> al_store L + 8388608 <= ATOP ->
  (t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) -> (t + 4096 <= al_store L \/ al_store L + 8388608 <= t) ->
  bv_unsigned sp < 2^47 ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 -> rng RNG hm 24 -> rng RNG (shad (hm + 16)) (shlen (rup n 8)) ->
  AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L -> iclr t 4096 ->      (* [comment removed for export] *)
  evtF asegs RNG (free_fast_post DI L ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n nb fst0 lst qb b1 actx lo m)
    (MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + -2272)) gp tp t0 t1 t2 (Z_to_bv 64 (t + 2128)) (Z_to_bv 64 (t + 208))
             (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 hm) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 n) (Z_to_bv 64 Q_CACHE)
             s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x38360) fc None m (seg_rom asegs)).
Section Zd2.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 0).
Variable full : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 1).
Variable g : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 2).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 3).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 4).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 5).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 6).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 7).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 8).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 9).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 10).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 11).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 12).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 13).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 14).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 15).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 16).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 17).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 18).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 19).
Variable ra0 : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 20).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 21).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 22).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 23).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 24).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 25).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 26).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 27).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 28).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 29).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 30).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 31).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 32).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 33).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 34).
Variable F : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 35).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 36).
Variable m : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 37).
Variable t : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 38).
Variable hm : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 39).
Variable n : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 40).
Variable b1 : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 41).
Variable actx : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 42).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 43).
Variable nb : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 44).
Variable fst0 : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 45).
Variable lst : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 46).
Variable qb : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 47).
Variable nx : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 48).
Variable bsz : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 49).
Variable cnt : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 50).
Variable spacebeg : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 51).
Variable id : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 52).
Variable b : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 53).
Variable maxc : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 54).
Variable csz : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 55).
Variable stj : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 56).
Variable idxw : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 57).
Variable sj : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 58).
Variable tb : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 59).
Variable chunks : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 60).
Variable hs : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 61).
Variable junk2 : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 62).
Variable j0 : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 63).
Variable trt : ltac2:(SecDietF.SzSecF.ty 'free_from_refill_spec__stmt 64).
Let sp1 := Z_to_bv 64 (bv_unsigned sp + -2128).
#[using="sp1"] Lemma free_from_refill_spec__body : ltac:(let T := type of (fun (h : free_from_refill_spec__stmt) => h L full g RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m t hm n b1 actx lo nb fst0 lst qb nx bsz cnt spacebeg id b maxc csz stj idxw sj tb chunks hs junk2 j0 trt) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (full, (g, (RNG, (ra, (sp, (gp, (tp, (s0, (s1, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (ra0, (t0, (t1, (t2, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (t3, (t4, (t5, (t6, (F, (fc, (m, (t, (hm, (n, (b1, (actx, (lo, (nb, (fst0, (lst, (qb, (nx, (bsz, (cnt, (spacebeg, (id, (b, (maxc, (csz, (stj, (idxw, (sj, (tb, (chunks, (hs, (junk2, (j0, trt))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) as _.
 cbv zeta.
  intros ST CEIL LO MI SS TB LTB FRS FRP FRE QK HD FC IDR N AL HLO TCH HHI HCE SH QC NB QB QBN FST LST T0 T1 TAL DHT STATS LSJ UW FL IAS IAM
         FULL SB CR CH LCH CNT NTH IXS STS HBE BJ SBP B0 BL1 DTB DTL DBL DHB DHL RB ES DK DS DEP N0 N1 R0 R1 DTN DTS SP47
         RIMG RTLS RSTK RT RH RSH NI SI TI. band_lin.   (* [comment removed for export] *)
  band_int TI. (pose proof (ablk_lin _ _ HLO) as ndP__; nd_pre ndP__ 4%nat; intros HL1 HL2 HL3 HL4; nd_post). unfold AIMG_HI in HL1. band_int HLO. band_int T0. band_int N0. band_int R0.   (* [comment removed for export] *)
  assert (RUP : n <= rup n 8 <= n + 7 /\ rup n 8 mod 8 = 0) by (clear -N; unfold rup; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
  assert (SHB : 2148239360 <= shad (hm + 16) /\ shad (hm + 16) + shlen (rup n 8) <= 0x10007fff8000 /\ 0 < shlen (rup n 8)).
  { clear -N HLO HL1 HHI HCE. unfold shad, shlen, ASHOFF, rup in *. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold Q_MAX in *. Z.div_mod_to_equations. lia. }
  (pose proof (dk_pre_pure _ g RNG L t lst hm (qb + (n + 8192)) m DK DS TI ltac:(unfold AIMG_HI; lia) NI SI
                DHL DTL ltac:(cbn [ek_seps] in ES; destruct full; [destruct ES as (_ & _ & _ & S4); destruct FULL as (_ & _ & _ & _ & L0 & _); exact (proj1 (proj2 (S4 eq_refl))) | destruct FULL as [_ ->]; unfold AIMG_HI in *; lia])
                ltac:(cbn [ek_seps] in ES; destruct full; [destruct ES as (_ & _ & _ & S4); exact (proj2 (proj2 (S4 eq_refl))) | destruct FULL as [_ ->]; unfold AIMG_HI in *; lia])
                ltac:(destruct full; [destruct FULL as (_ & _ & _ & _ & L0 & _) | destruct FULL as [_ ->]]; unfold AIMG_HI in *; lia)
                ltac:(destruct full; [destruct FULL as (_ & _ & _ & _ & L0 & L1 & _) | destruct FULL as [_ ->]]; unfold AIMG_HI in *; atop_facts; lia)
                ltac:(destruct full; [destruct FULL as (_ & _ & _ & _ & L0 & _); right | destruct FULL as [_ ->]; left]; unfold AIMG_HI in *; lia)) as ndP__; nd_pre ndP__ 7%nat; intros DF1 DF2 DF3 DF4 DG0 DG1 DG2; nd_post).
  cbn [ek_seps] in ES. (nd_pre ES 4%nat; intros SB1 SB2 SB3 SL; nd_post).
  assert (PL2 : lst = 0 \/ 0x10007fff8000 <= lst) by (destruct full; [(nd_pre FULL 6%nat; intros _ _ _ _ L0 _; nd_post); right; exact L0 | destruct FULL as [_ E0]; left; exact E0]).
  assert (PLB : lst + 8192 <= ATOP) by (destruct full; [(nd_pre FULL 7%nat; intros _ _ _ _ _ L1 _; nd_post); exact L1 | destruct FULL as [_ E0]; rewrite E0; atop_facts; lia]).
  (pose proof (qsz_int lst ltac:(clear -PL2; lia) ltac:(clear -PLB; atop_facts; lia)) as ndP__; nd_pre ndP__ 5%nat; intros zq QZ0 QZ1 QZ2 QZ3; nd_post).   (* [comment removed for export] *)
  unfold AIMG_HI, AFREE_SYM, AFREE_PC in *.
  word_range sp SPR.
  box DHT. box DTN. box DTS. box DTB. box DTL. box DBL. box DHB. box DHL. box SB1. box SB2. box SB3. box DF1. box DF2. box DF3. box DF4. box DG2. box PL2.
  (* [comment removed for export] *)
  chg (Z_to_bv 64 (bv_unsigned sp + -2128)) sp1.
  assert (Hsp : bv_unsigned sp1 = bv_unsigned sp + -2128) by (subst sp1; apply unsigned_lit; lia).
  replace (bv_unsigned sp + -2272) with (bv_unsigned sp1 + -144) in * by lia.
  replace (bv_unsigned sp + -2208) with (bv_unsigned sp1 + -80) in * by lia.
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (put_from_refill_spec full g t hm lst b RNG (Z_to_bv 64 0x56394) sp1 gp tp sp (Z_to_bv 64 (hm + 16)) (Z_to_bv 64 (t + 208)) sp1
              (Z_to_bv 64 0x56324) (Z_to_bv 64 1) sp1 (Z_to_bv 64 (bv_unsigned sp + -81)) s6 s7 s8 s9 s10 s11
              ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m n nb fst0 qb b1 actx lo nx bsz cnt spacebeg maxc csz stj idxw chunks hs j0).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact ST | exact IAS]
         | |- mem_inv _ _ => exact MI
         | |- if _ then _ else _ => exact FULL
         | |- dk_pre _ _ _ _ _ _ _ _ => exact DK
         | |- @eq word _ _ => reflexivity
         | |- @eq Z _ _ => first [exact HBE | lia]
         | |- ex _ => exact BJ
         | |- _ \/ _ => first [ub DHT; ylia | ub DTB; ylia | ub DTL; ylia | ub DBL; ylia | ub DHB; ylia | ub DHL; ylia]
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD
         | |- rw_cells _ _ (shad _) _ => exact SH
         | |- rw_cells _ _ (_ + 80) _ => exact QC
         | |- rw_cells _ _ (_ + 2128) _ => exact CR
         | |- rw_cells _ _ (_ + 2784) _ => exact STS
         | |- rw_cells _ _ (_ + -80) _ => exact FRP
         | |- iclr _ _ => exact TI
         | |- rw_cells _ _ (_ + -144) _ => exact FRE
         | |- u32arr _ _ _ _ => exact CH
         | |- nth_error _ _ = _ => exact NTH
         end.
    all: try eassumption. all: try (unfold AIMG_HI, Q_MAX in *; lia).
    all: match goal with |- ?G => idtac "REMQ" G end. }
  cbv beta. intros ms2 PP. unfold put_tail_post in PP.
  (nd_pre PP 17%nat; intros t0b t1b t2b a0b a1b a2b a3b a4b a5b a6b a7b t3b t4b t5b t6b m2 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 9%nat; intros MUp WMp MIp STp SH2 HD2 QC2 EKP DKP; nd_post).
  replace (ret_pc (Z_to_bv 64 353172)) with (Z_to_bv 64 353172) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  (* [comment removed for export] *)
  cbn [ek_b] in MUp.
  xport FC MUp WMp ltac:(ub DHT; ub DHB; ub DHL; ub DF1; ylia).
  xport STATS MUp WMp ltac:(rewrite LSJ; ub DTB; ub DTL; ub DF2; ylia).
  xport UW MUp WMp ltac:(ub DTB; ub DTL; ub DF2; ylia).
  xport FL MUp WMp ltac:(ub DG2; ub PL2; ylia). xport IAS MUp WMp ltac:(ub DG2; ub PL2; ylia).
  xport SS MUp WMp ltac:(lia). xport TB MUp WMp ltac:(rewrite LTB; lia). xport FRS MUp WMp ltac:(lia).
  assert (IAM2 : forall j, 0 <= j < 32768 -> bytes_at asegs m2 (0xafc08 + 8 * j) (le8 (Z_to_bv 64 0))).
  { (intros j Hj; eapply bytes_at_agree; [exact (IAM j Hj)|];
    intros i Hi; apply MUp; cbn [outside]; rewrite length_le8 in Hi; rewrite wa_unsigned by lia; ub DG2; ub PL2; ylia). }
  clear IAM.
  assert (DEP2 : ADEPOT DI L m2).
  { eapply (adi_frame DI); [exact DEP | exact MUp | exact WMp |].
    ((first [ apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [ lia |lia | ub DTN; ub DTS; ylia | ub SB2; ub SB3; ylia | ub DF3; ub DF4; ub DG2; ylia
            | destruct full; [(nd_pre (SL eq_refl) 3%nat; intros _ S6 S7; nd_post); lia | destruct FULL as [_ LST0]; lia] ] | first [ apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [ lia |lia | ub DTN; ub DTS; ylia | ub SB2; ub SB3; ylia | ub DF3; ub DF4; ub DG2; ylia
            | destruct full; [(nd_pre (SL eq_refl) 3%nat; intros _ S6 S7; nd_post); lia | destruct FULL as [_ LST0]; lia] ] | first [ apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [ ub DTN; ub DTS; ylia |lia | ub DTN; ub DTS; ylia | ub SB2; ub SB3; ylia | ub DF3; ub DF4; ub DG2; ylia
            | destruct full; [(nd_pre (SL eq_refl) 3%nat; intros _ S6 S7; nd_post); lia | destruct FULL as [_ LST0]; lia] ] | first [ apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [ ub DTN; ub DTS; ylia |lia | ub DTN; ub DTS; ylia | ub SB2; ub SB3; ylia | ub DF3; ub DF4; ub DG2; ylia
            | destruct full; [(nd_pre (SL eq_refl) 3%nat; intros _ S6 S7; nd_post); lia | destruct FULL as [_ LST0]; lia] ] | first [ apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [ ub DTN; ub DTS; ylia |lia | ub DTN; ub DTS; ylia | ub SB2; ub SB3; ylia | ub DF3; ub DF4; ub DG2; ylia
            | destruct full; [(nd_pre (SL eq_refl) 3%nat; intros _ S6 S7; nd_post); lia | destruct FULL as [_ LST0]; lia] ] | first [ apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [ destruct full; [(nd_pre (SL eq_refl) 3%nat; intros _ S6 S7; nd_post); lia | destruct FULL as [_ LST0]; lia] |lia | ub DTN; ub DTS; ylia | ub SB2; ub SB3; ylia | ub DF3; ub DF4; ub DG2; ylia
            | destruct full; [(nd_pre (SL eq_refl) 3%nat; intros _ S6 S7; nd_post); lia | destruct FULL as [_ LST0]; lia] ] | first [ apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [ ub SB2; ub SB3; ylia |lia | ub DTN; ub DTS; ylia | ub SB2; ub SB3; ylia | ub DF3; ub DF4; ub DG2; ylia
            | destruct full; [(nd_pre (SL eq_refl) 3%nat; intros _ S6 S7; nd_post); lia | destruct FULL as [_ LST0]; lia] ] | first [ apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [ lia |lia | ub DTN; ub DTS; ylia | ub SB2; ub SB3; ylia | ub DF3; ub DF4; ub DG2; ylia
            | destruct full; [(nd_pre (SL eq_refl) 3%nat; intros _ S6 S7; nd_post); lia | destruct FULL as [_ LST0]; lia] ] | first [ apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [ lia |lia | ub DTN; ub DTS; ylia | ub SB2; ub SB3; ylia | ub DF3; ub DF4; ub DG2; ylia
            | destruct full; [(nd_pre (SL eq_refl) 3%nat; intros _ S6 S7; nd_post); lia | destruct FULL as [_ LST0]; lia] ] | first [ apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [ ub DF3; ub DF4; ub DG2; ylia |lia | ub DTN; ub DTS; ylia | ub SB2; ub SB3; ylia | ub DF3; ub DF4; ub DG2; ylia
            | destruct full; [(nd_pre (SL eq_refl) 3%nat; intros _ S6 S7; nd_post); lia | destruct FULL as [_ LST0]; lia] ] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub SB2; ub SB3; ylia | ub DF3; ub DF4; ub DG2; ylia
            | destruct full; [(nd_pre (SL eq_refl) 3%nat; intros _ S6 S7; nd_post); lia | destruct FULL as [_ LST0]; lia] ] |])] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub SB2; ub SB3; ylia | ub DF3; ub DF4; ub DG2; ylia
            | destruct full; [(nd_pre (SL eq_refl) 3%nat; intros _ S6 S7; nd_post); lia | destruct FULL as [_ LST0]; lia] ] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub SB2; ub SB3; ylia | ub DF3; ub DF4; ub DG2; ylia
            | destruct full; [(nd_pre (SL eq_refl) 3%nat; intros _ S6 S7; nd_post); lia | destruct FULL as [_ LST0]; lia] ] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub SB2; ub SB3; ylia | ub DF3; ub DF4; ub DG2; ylia
            | destruct full; [(nd_pre (SL eq_refl) 3%nat; intros _ S6 S7; nd_post); lia | destruct FULL as [_ LST0]; lia] ] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub SB2; ub SB3; ylia | ub DF3; ub DF4; ub DG2; ylia
            | destruct full; [(nd_pre (SL eq_refl) 3%nat; intros _ S6 S7; nd_post); lia | destruct FULL as [_ LST0]; lia] ] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub SB2; ub SB3; ylia | ub DF3; ub DF4; ub DG2; ylia
            | destruct full; [(nd_pre (SL eq_refl) 3%nat; intros _ S6 S7; nd_post); lia | destruct FULL as [_ LST0]; lia] ] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub SB2; ub SB3; ylia | ub DF3; ub DF4; ub DG2; ylia
            | destruct full; [(nd_pre (SL eq_refl) 3%nat; intros _ S6 S7; nd_post); lia | destruct FULL as [_ LST0]; lia] ] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub SB2; ub SB3; ylia | ub DF3; ub DF4; ub DG2; ylia
            | destruct full; [(nd_pre (SL eq_refl) 3%nat; intros _ S6 S7; nd_post); lia | destruct FULL as [_ LST0]; lia] ] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub SB2; ub SB3; ylia | ub DF3; ub DF4; ub DG2; ylia
            | destruct full; [(nd_pre (SL eq_refl) 3%nat; intros _ S6 S7; nd_post); lia | destruct FULL as [_ LST0]; lia] ] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub SB2; ub SB3; ylia | ub DF3; ub DF4; ub DG2; ylia
            | destruct full; [(nd_pre (SL eq_refl) 3%nat; intros _ S6 S7; nd_post); lia | destruct FULL as [_ LST0]; lia] ] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; ylia | ub SB2; ub SB3; ylia | ub DF3; ub DF4; ub DG2; ylia
            | destruct full; [(nd_pre (SL eq_refl) 3%nat; intros _ S6 S7; nd_post); lia | destruct FULL as [_ LST0]; lia] ] |]) ]); apply Forall_nil). }
  clear DEP.
  (* [comment removed for export] *)
  subst sp1. rewrite ?unsigned_lit in STp by lia. rewrite ?unsigned_lit in MUp by lia.
  apply rw_cells_of_u64arr in TB. rewrite LTB in TB.
  eapply evtF_mono.
  { (eapply (ficptD_spec RNG sp gp tp); [exact STp | atop_facts; lia | lia | exact MIp
      | eexists; split; [exact SS | reflexivity]
      | eexists; split; [replace (bv_unsigned sp + -2112) with (bv_unsigned sp + -2128 + 16) by lia; exact TB | reflexivity]
      | exact FRS | exact RIMG | exact RTLS | solve_rng ]). }
  cbv beta. intros ms3 [-> ST3].
  (* [comment removed for export] *)
  assert (MU : munch (free_W L sp t hm n lst (EkNew full nx bsz cnt maxc csz stj idxw chunks spacebeg b hs) g) m m2).
  { eapply munch_weaken; [| exact MUp]. cbn [ek_b]. solve_sub_fp sp. }
  unfold free_fast_post. exists id. do 15 eexists. exists m2, sj.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WMp|]. split; [exact MIp|]. split; [exact ST3|]. split; [exact IDR|].
  split; [exact HD2|]. split; [exact FC|]. split; [exact SH2|]. split; [exact QC2|]. split; [exact EKP|]. split; [exact DKP|].
  split; [exact STATS|]. split; [exact LSJ|]. split; [exact UW|]. split; [exact FL|]. split; [exact IAS|]. split; [exact IAM2|].
  exact DEP2.
  Unshelve. all: try exact ST; try exact STp.
Qed.
End Zd2.
#[using="Type"] Lemma free_from_refill_spec : ltac:(let t := eval cbv delta [free_from_refill_spec__stmt] in free_from_refill_spec__stmt in exact t).
Proof. exact free_from_refill_spec__body. Qed.
End WithDepot.
End CANSEC1.
End TwB.
End F_afree_icptR.

(* [comment removed for export] *)
Module F_afreeC_iface.
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecSlog__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_adrain__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_front__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_tail. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_afree_iseg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_front OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_adrain OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tail OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_icpt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_aenqueueR OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tailR__A3W.F_afree_tailR OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tailR__A3W.F_afree_icptR.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition drain_torec_post (gfull : bool) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 : word) (F : bvmap 5 word) (fc : bv 32)
    (t nb fst lst qb gnb gfst glst gqb lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 AQUAR_Q) (Z_to_bv 64 Q_MIN) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x35aa0) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (t + 80, t + 112); (0xab308, 0xab308 + 4); (0xab310, 0xab310 + 32); (glst, glst + 8)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (t + 80) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells asegs m' 0xab308 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ rw_cells asegs m' 0xab310 [C8 (Z_to_bv 64 (gnb + nb)); C8 (Z_to_bv 64 (if gfull then gfst else fst)); C8 (Z_to_bv 64 lst);
                                   C8 (Z_to_bv 64 (gqb + qb))]
    /\ (if gfull then rw_cells asegs m' glst [C8 (Z_to_bv 64 fst)] else True).

Definition drain_torec_stmt : Prop := forall (gfull : bool) (t glst : Z) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (nb fst lst qb gnb gfst gqb gnx lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 AQUAR_Q -> a1 = Z_to_bv 64 (t + 80) ->
  rw_cells asegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 < nb < 2^63 -> 0 <= qb -> 0 <= fst < 2^64 -> 0 <= lst < 2^64 ->
  rw_cells asegs m AQ_MUTEX [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m AQ_GCACHE [C8 (Z_to_bv 64 gnb); C8 (Z_to_bv 64 gfst); C8 (Z_to_bv 64 glst); C8 (Z_to_bv 64 gqb)] ->
  0 <= gnb < 2^62 -> 0 <= gqb -> Q_MAX < gqb + qb -> gqb + qb < 2^63 -> 0 <= gfst < 2^64 -> 0 <= glst < 2^64 ->
  rw_cells asegs m AQ_MAX [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->
  (if gfull then 0 < gnb /\ rw_cells asegs m glst [C8 (Z_to_bv 64 gnx)] /\ AIMG_HI <= glst /\ glst + Q_BATCH_BYTES <= ATOP
                 /\ (t + 4096 <= glst \/ glst + Q_BATCH_BYTES <= t)
   else gnb = 0) ->
  iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 -> (if gfull then rng RNG glst Q_BATCH_BYTES else True) ->
  evtF asegs RNG (drain_torec_post gfull ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 F fc t nb fst lst qb gnb gfst glst gqb lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x358fc) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dk_preC (ek : enq_kind) (g : gqd) (RNG : footprint) (t lst hm qb' : Z) (m : amem) : Prop :=
     g_drain g = true
  /\ rw_cells asegs m 0xab308 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
  /\ rw_cells asegs m 0xab310 [C8 (Z_to_bv 64 (g_nb g)); C8 (Z_to_bv 64 (g_fst g)); C8 (Z_to_bv 64 (g_lst g)); C8 (Z_to_bv 64 (g_qb g))]
  /\ 0 <= g_nb g < 2^62 /\ 0 <= g_qb g /\ 0 <= g_fst g < 2^64 /\ 0 <= g_lst g < 2^64
  /\ Q_CACHE < qb' /\ Q_MAX < g_qb g + qb' /\ g_qb g + qb' < 2^63
  /\ (if g_full g then 0 < g_nb g /\ rw_cells asegs m (g_lst g) [C8 (Z_to_bv 64 (g_nx g))] /\ 0x10007fff8000 <= g_lst g /\ g_lst g + 8192 <= ATOP
                     /\ (t + 4096 <= g_lst g \/ g_lst g + 8192 <= t) /\ (hm + 16 <= g_lst g \/ g_lst g + 8 <= hm)
                     /\ (lst + 8192 <= g_lst g \/ g_lst g + 8192 <= lst) /\ (ek_b ek lst + 8192 <= g_lst g \/ g_lst g + 8192 <= ek_b ek lst)
                     /\ rng RNG (g_lst g) 8192
      else g_nb g = 0 /\ g_lst g = 0).

Definition dk_postC (g : gqd) (nb' fst' lst' qb' : Z) (m' : amem) : Prop :=
     rw_cells asegs m' 0xab308 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
  /\ rw_cells asegs m' 0xab310 [C8 (Z_to_bv 64 (g_nb g + nb')); C8 (Z_to_bv 64 (if g_full g then g_fst g else fst'));
                                 C8 (Z_to_bv 64 lst'); C8 (Z_to_bv 64 (g_qb g + qb'))]
  /\ (if g_full g then rw_cells asegs m' (g_lst g) [C8 (Z_to_bv 64 fst')] else True).

(* [comment removed for export] *)
Definition put_frame (cbc cbs s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
  [C8 cbc; C8 cbs; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition put_torec_post (ek : enq_kind) (g : gqd)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 : word) (F : bvmap 5 word) (fc : bv 32)
    (t hm n nb fst0 lst qb b1 actx lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 xs0 xs1 xs2 xs3 xs4 xs5 xs6 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR (Z_to_bv 64 0x380d0) (Z_to_bv 64 (bv_unsigned sp - 80)) gp tp t0 t1 t2 xs0 xs1
                  (Z_to_bv 64 AQUAR_Q) (Z_to_bv 64 Q_MIN) (Z_to_bv 64 (t + 208)) a3 a4 a5 a6 a7 xs2 xs3 xs4 xs5 xs6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x35aa0) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 144, bv_unsigned sp); (shad (hm + 16), shad (hm + 16) + shlen (rup n 8));
              (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792);
              (lst, lst + qsz lst); (ek_b ek lst, ek_b ek lst + 8192);
              (0xab308, 0xab308 + 4); (0xab310, 0xab310 + 32); (dk_glst g lst, dk_glst g lst + 8)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp - 80)
    /\ rw_cells asegs m' (bv_unsigned sp - 80) (put_frame (Z_to_bv 64 (t + 208)) a3 s6 s5 s4 s3 s2 s1 s0 ra)
    /\ rw_cells asegs m' (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) (repeat (Z_to_bv 8 253) (Z.to_nat (shlen (rup n 8))))]
    /\ rw_cells asegs m' hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)]
    /\ rw_cells asegs m' (t + 80) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ ek_post ek t lst hm n m'
    /\ dk_postC g (ek_nb ek nb) (ek_fst ek fst0) (ek_lst ek lst) (qb + ek_delta ek n) m'.

(* [comment removed for export] *)
Definition put_torec_stmt : Prop := forall (ek : enq_kind) (g : gqd) (t hm lst : Z) RNG
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n nb fst0 qb b1 actx lo : Z) (sjunk : list byte),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 144 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 0xab270 -> a1 = Z_to_bv 64 (t + 80) -> a2 = Z_to_bv 64 (t + 208) -> a4 = Z_to_bv 64 hm -> a5 = Z_to_bv 64 n ->
  rw_cells asegs m 0xab2b0 [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->
  rw_cells asegs m 0xa54a8 [C8 (Z_to_bv 64 AFLAGS)] ->
  rw_cells asegs m 0xabe24 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->
  poison_cells m ->
  rw_cells asegs m hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  1 <= n <= Q_MAX -> 0 <= b1 < 256 -> hm mod 16 = 0 -> ablk hm (hm + 16 + rup n 8) -> tclr hm 24 -> hm + 16 + rup n 8 <= ATOP -> hm + 16 <= ATOP ->
  rw_cells asegs m (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) sjunk] ->
  rw_cells asegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= qb -> qb + n + 8192 < 2^62 -> 0 <= fst0 < 2^64 -> 0 <= lst < 2^64 ->
  sclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> t mod 4096 = 0 -> (hm + 16 <= t \/ t + 4096 <= hm) ->
  ek_pre ek RNG t nb lst n hm m ->
  dk_preC ek g RNG t lst hm (qb + ek_delta ek n) m ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 -> rng RNG hm 16 -> rng RNG (shad (hm + 16)) (shlen (rup n 8)) ->
  iclr t 4096 ->                                            (* [comment removed for export] *)
  evtF asegs RNG (put_torec_post ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 F fc t hm n nb fst0 lst qb b1 actx lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x37ff4) fc None m (seg_rom asegs)).


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition put_from_refill_torec_stmt : Prop := forall (full : bool) (g : gqd) (t hm lst b : Z) RNG
    (ra sp gp tp s0 s1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (ra0 t0 t1 t2 a1 a2' a3' a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : amem) (n nb fst0 qb b1 actx lo nx bsz cnt spacebeg : Z) (maxc csz stj idxw : word) (chunks hs : list word)
    (j0 : list byte),
  let ek := EkNew full nx bsz cnt maxc csz stj idxw chunks spacebeg b hs in
  stk asegs m lo (bv_unsigned sp + -144) -> ATOP <= lo -> lo <= bv_unsigned sp - 144 ->
  mem_inv asegs m ->
  a2 = Z_to_bv 64 (t + 208) ->
  (* [comment removed for export] *)
  rw_cells asegs m (bv_unsigned sp + -80) [C8 a2; C8 a3; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m (bv_unsigned sp + -144)
     [CB 8 j0; C8 (Z_to_bv 64 hm); C8 a2; C8 a3; C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 (t + 80)); C8 (Z_to_bv 64 0xab270); C8 (Z_to_bv 64 0x38198)] ->
  (* [comment removed for export] *)
  rw_cells asegs m 0xab2b0 [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->
  (* [comment removed for export] *)
  rw_cells asegs m hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  1 <= n <= Q_MAX -> hm mod 16 = 0 -> ablk hm (hm + 16 + rup n 8) -> tclr hm 24 -> hm + 16 + rup n 8 <= ATOP -> hm + 16 <= ATOP ->
  rw_cells asegs m (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) (repeat (Z_to_bv 8 253) (Z.to_nat (shlen (rup n 8))))] ->
  (* [comment removed for export] *)
  rw_cells asegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= qb -> qb + n + 8192 < 2^62 -> 0 <= fst0 < 2^64 -> 0 <= lst < 2^64 ->
  sclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> t mod 4096 = 0 -> (hm + 16 <= t \/ t + 4096 <= hm) ->
  (* [comment removed for export] *)
  (if full then 0 < nb /\ rw_cells asegs m lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)]
             /\ 0 <= nx < 2^64 /\ 0 <= bsz < 2^64 /\ 0x10007fff8000 <= lst /\ lst + 8192 <= ATOP
             /\ u64arr asegs m (lst + 24) hs /\ length hs = 1021%nat
             /\ rng RNG lst 8192
   else nb = 0 /\ lst = 0) ->
  rw_cells asegs m 0xaafb8 [C8 (Z_to_bv 64 spacebeg)] ->
  rw_cells asegs m (t + 2128) [C4 (Z_to_bv 64 cnt); C4 maxc; C8 csz] ->
  u32arr asegs m (t + 2128 + 16) chunks -> length chunks = 16%nat ->
  0 < cnt <= 16 -> nth_error chunks (Z.to_nat (cnt - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
  rw_cells asegs m (t + 2784) [C8 stj] ->
  b = spacebeg + 24 * 2^32 + 16 * bv_unsigned idxw ->
  (exists bs, rw_cells asegs m b [CB (Z.to_nat 8192) bs]) ->
  0 < spacebeg -> 0x10007fff8000 <= b -> b + 8192 <= ATOP ->
  (t + 4096 <= b \/ b + 8192 <= t) -> (t + 4096 <= lst \/ lst + 8192 <= t \/ lst = 0) -> (b + 8192 <= lst \/ lst + 8192 <= b) ->
  (hm + 16 <= b \/ b + 8192 <= hm) -> (hm + 16 <= lst \/ lst + 8192 <= hm) ->
  rng RNG b 8192 ->
  (* [comment removed for export] *)
  dk_preC ek g RNG t lst hm (qb + ek_delta ek n) m ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 -> rng RNG hm 16 -> rng RNG (shad (hm + 16)) (shlen (rup n 8)) ->
  iclr t 4096 ->                                            (* [comment removed for export] *)
  evtF asegs RNG (put_torec_post ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 F fc t hm n nb fst0 lst qb b1 actx lo m)
    (MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 (Z_to_bv 64 (t + 2128)) (Z_to_bv 64 (t + 208))
             (Z_to_bv 64 1) a1 a2' a3' a4 a5 a6 a7
             (Z_to_bv 64 hm) (Z_to_bv 64 (t + 80)) a3 (Z_to_bv 64 n) (Z_to_bv 64 Q_CACHE) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x382f8) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithDepot.
Variable DI : ADepotIface.

(* [comment removed for export] *)
Definition free_torec_post (L : alayout) (ek : enq_kind) (g : gqd)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t hm n nb fst0 lst qb b1 actx lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (id : Z) (t0 t1 t2 xs0 xs1 xs2 xs3 xs4 xs5 xs6 ps0 ps1 ps2 ps3 ps4 ps5 spv a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m' (sj' : list word)
                    (csA csT : list cell) (junk2 : list byte),
    let spP := bv_unsigned sp - 2128 in
    ms' = MS (mkR (Z_to_bv 64 0x380d0) (Z_to_bv 64 (spP - 80)) gp tp t0 t1 t2 xs0 xs1
                  (Z_to_bv 64 AQUAR_Q) (Z_to_bv 64 Q_MIN) (Z_to_bv 64 (t + 208)) a3 a4 a5 a6 a7 xs2 xs3 xs4 xs5 xs6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x35aa0) fc None m' (seg_rom asegs)
    /\ munch ([(bv_unsigned sp - 4096, bv_unsigned sp); (0xaf800, 0xaf800 + 0x81030); (0x13e088, 0x13e088 + 4);
               (t + 3168, t + 3169); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368);
               (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608);
               (shad (hm + 16), shad (hm + 16) + shlen (rup n 8)); (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792);
               (lst, lst + qsz lst); (ek_b ek lst, ek_b ek lst + 8192);
               (0xab308, 0xab308 + 4); (0xab310, 0xab310 + 32); (dk_glst g lst, dk_glst g lst + 8)]%Z) m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (spP - 80)
    /\ 0 < id < 2^31
    (* [comment removed for export] *)
    /\ rw_cells asegs m' (spP - 80) (put_frame (Z_to_bv 64 (t + 208)) a3 s6 ps5 ps4 ps3 ps2 ps1 ps0 (Z_to_bv 64 353068))
    (* [comment removed for export] *)
    /\ rw_cells asegs m' spP csA /\ cells_size csA = 16%nat
    /\ rw_cells asegs m' (spP + 16) csT /\ cells_size csT = 2040%nat
    /\ rw_cells asegs m' (bv_unsigned sp - 72) [C8 spv; CB 8 junk2; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)]
    /\ rw_cells asegs m' (hm + 16) [C8 (Z_to_bv 64 id)]
    /\ rw_cells asegs m' (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) (repeat (Z_to_bv 8 253) (Z.to_nat (shlen (rup n 8))))]
    /\ rw_cells asegs m' (t + 80) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ ek_post ek t lst hm n m'
    /\ dk_postC g (ek_nb ek nb) (ek_fst ek fst0) (ek_lst ek lst) (qb + ek_delta ek n) m'
    /\ u64arr asegs m' (t + 2800) sj' /\ length sj' = 46%nat
    /\ rw_cells asegs m' (t + 3168) [C1 (Z_to_bv 8 0)]
    /\ rw_cells asegs m' 0x13e088 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ stk asegs m' 0xaf800 (0xaf800 + 0x81030)
    /\ (forall j, 0 <= j < 32768 -> bytes_at asegs m' (0xaf808 + 8 * j) (le8 (Z_to_bv 64 0)))
    /\ ADEPOT DI L m'.

(* [comment removed for export] *)
Definition free_torec_stmt : Prop := forall (L : alayout) (ia : bool) (ek : enq_kind) (g : gqd) RNG
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem)
    (t ctx hm n b1 actx lo top bot nb fst0 lst qb : Z) (uw : word) (sj : list word) (sjunk : list byte) (trt : list Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 (hm + 16) ->
  bv_unsigned sp mod 16 = 0 ->
  allocA_cells m ctx t -> poison_cells m ->
  rw_cells asegs m 0xaf2fc [C4 (Z_to_bv 64 30)] ->
  rw_cells asegs m 0x14014a [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m 0xa5490 [C8 (Z_to_bv 64 0x13e0a0)] -> rw_cells asegs m 0x13e0a0 [C8 (Z_to_bv 64 4096)] ->
  rw_cells asegs m 0x1400c8 [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m 0xab2b0 [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->
  rw_cells asegs m 0xa54a8 [C8 (Z_to_bv 64 AFLAGS)] ->
  rw_cells asegs m 0xabe24 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->
  rw_cells asegs m 0x13e088 [C1 (Z_to_bv 8 (if ia then 1 else 0)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  stk asegs m 0xaf800 (0xaf800 + 0x81030) ->
  (ia = true -> forall j, 0 <= j < 32768 -> bytes_at asegs m (0xaf808 + 8 * j) (le8 (Z_to_bv 64 0))) ->
  rw_cells asegs m (ctx + 8) [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m t [C8 (Z_to_bv 64 ctx); C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)] ->
  rw_cells asegs m (t + 40) [C1 (Z_to_bv 8 0)] -> rw_cells asegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  rw_cells asegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= qb -> qb + n + 8192 < 2^62 -> 0 <= fst0 < 2^64 -> 0 <= lst < 2^64 ->
  0 < ctx -> sclr ctx 65536 -> ctx + 4096 <= ATOP ->
  sclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> t mod 4096 = 0 -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  rw_cells asegs m hm [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  rw_cells asegs m (hm + 16) [C8 uw] -> 0 <= b1 < 256 -> Z.land b1 3 = 1 -> 1 <= n <= Q_MAX -> hm mod 16 = 0 ->
  ablk hm (hm + 16 + rup n 8) -> tclr hm 24 -> hm + 16 + rup n 8 <= ATOP -> hm + 24 <= ATOP ->
  rw_cells asegs m (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) sjunk] ->
  (hm + 24 <= t \/ t + 4096 <= hm) -> (hm + 24 <= ctx \/ ctx + 4096 <= hm) ->
  ek_pre ek RNG t nb lst n hm m -> ek_seps ek L hm lst ->
  dk_preC ek g RNG t lst hm (qb + ek_delta ek n) m -> dk_seps g L hm ->
  ADEPOT DI L m ->
  sclr (al_nodes L) 1048576 -> al_nodes L + 1048576 <= ATOP -> sclr (al_store L) 8388608 -> al_store L + 8388608 <= ATOP ->
  (hm + 24 <= al_nodes L \/ al_nodes L + 1048576 <= hm) -> (hm + 24 <= al_store L \/ al_store L + 8388608 <= hm) ->
  (t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) -> (t + 4096 <= al_store L \/ al_store L + 8388608 <= t) ->
  (ctx + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= ctx) -> (ctx + 4096 <= al_store L \/ al_store L + 8388608 <= ctx) -> tclr (al_nodes L) 1048576 -> tclr (al_store L) 8388608 ->
  afree_unw RNG lo m top sp s0 ra trt ->
  bv_unsigned s0 <> bv_unsigned sp + 8 ->
  In (AFREE_PC :: trt) (al_U L) ->
  0 <= bot -> bot < bv_unsigned sp -> bot < top -> 4096 <= top <= 2^47 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 -> rng RNG hm 24 -> rng RNG (shad (hm + 16)) (shlen (rup n 8)) ->
  AIMG_HI <= ctx -> AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L -> iclr t 4096 ->      (* [comment removed for export] *)
  evtF asegs RNG (free_torec_post L ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n nb fst0 lst qb b1 actx lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
Definition free_from_refill_torec_stmt : Prop := forall (L : alayout) (full : bool) (g : gqd) RNG
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : amem)
    (t hm n b1 actx lo nb fst0 lst qb nx bsz cnt spacebeg id b : Z) (maxc csz stj idxw : word) (sj tb chunks hs : list word)
    (junk2 j0 : list byte) (trt : list Z),
  let ek := EkNew full nx bsz cnt maxc csz stj idxw chunks spacebeg b hs in
  stk asegs m lo (bv_unsigned sp + -2272) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
  mem_inv asegs m ->
  (* [comment removed for export] *)
  rw_cells asegs m (bv_unsigned sp + -2128) [C8 (Z_to_bv 64 (bv_unsigned sp + -2128 + 16)); C4 (Z_to_bv 64 (1 + Z.of_nat (length trt))); C4 (Z_to_bv 64 0)] ->
  u64arr asegs m (bv_unsigned sp + -2128 + 16) tb -> length tb = 255%nat ->
  rw_cells asegs m (bv_unsigned sp + -72) [C8 sp; CB 8 junk2; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m (bv_unsigned sp + -2208)
     [C8 (Z_to_bv 64 (t + 208)); C8 (Z_to_bv 64 (bv_unsigned sp + -2128)); C8 s6; C8 (Z_to_bv 64 (bv_unsigned sp + -81));
      C8 (Z_to_bv 64 (bv_unsigned sp + -2128)); C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 0x562bc); C8 (Z_to_bv 64 (hm + 16)); C8 sp; C8 (Z_to_bv 64 0x5632c)] ->
  rw_cells asegs m (bv_unsigned sp + -2272)
     [CB 8 j0; C8 (Z_to_bv 64 hm); C8 (Z_to_bv 64 (t + 208)); C8 (Z_to_bv 64 (bv_unsigned sp + -2128)); C8 (Z_to_bv 64 n);
      C8 (Z_to_bv 64 (t + 80)); C8 (Z_to_bv 64 0xab270); C8 (Z_to_bv 64 0x38198)] ->
  (* [comment removed for export] *)
  rw_cells asegs m 0xab2b0 [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->
  (* [comment removed for export] *)
  rw_cells asegs m hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  rw_cells asegs m (hm + 16) [C8 (Z_to_bv 64 id)] -> 0 < id < 2^31 ->
  1 <= n <= Q_MAX -> hm mod 16 = 0 -> ablk hm (hm + 16 + rup n 8) -> tclr hm 24 -> hm + 16 + rup n 8 <= ATOP -> hm + 24 <= ATOP ->
  rw_cells asegs m (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) (repeat (Z_to_bv 8 253) (Z.to_nat (shlen (rup n 8))))] ->
  (* [comment removed for export] *)
  rw_cells asegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= qb -> qb + n + 8192 < 2^62 -> 0 <= fst0 < 2^64 -> 0 <= lst < 2^64 ->
  sclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> t mod 4096 = 0 -> (hm + 24 <= t \/ t + 4096 <= hm) ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat -> rw_cells asegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m 0x13e088 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  stk asegs m 0xaf800 (0xaf800 + 0x81030) ->
  (forall j, 0 <= j < 32768 -> bytes_at asegs m (0xaf808 + 8 * j) (le8 (Z_to_bv 64 0))) ->
  (* [comment removed for export] *)
  (if full then 0 < nb /\ rw_cells asegs m lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)]
             /\ 0 <= nx < 2^64 /\ 0 <= bsz < 2^64 /\ 0x10007fff8000 <= lst /\ lst + 8192 <= ATOP
             /\ u64arr asegs m (lst + 24) hs /\ length hs = 1021%nat
             /\ rng RNG lst 8192
   else nb = 0 /\ lst = 0) ->
  rw_cells asegs m 0xaafb8 [C8 (Z_to_bv 64 spacebeg)] ->
  rw_cells asegs m (t + 2128) [C4 (Z_to_bv 64 cnt); C4 maxc; C8 csz] ->
  u32arr asegs m (t + 2128 + 16) chunks -> length chunks = 16%nat ->
  0 < cnt <= 16 -> nth_error chunks (Z.to_nat (cnt - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
  rw_cells asegs m (t + 2784) [C8 stj] ->
  b = spacebeg + 24 * 2^32 + 16 * bv_unsigned idxw ->
  (exists bs, rw_cells asegs m b [CB (Z.to_nat 8192) bs]) ->
  0 < spacebeg -> 0x10007fff8000 <= b -> b + 8192 <= ATOP ->
  (t + 4096 <= b \/ b + 8192 <= t) -> (t + 4096 <= lst \/ lst + 8192 <= t \/ lst = 0) -> (b + 8192 <= lst \/ lst + 8192 <= b) ->
  (hm + 24 <= b \/ b + 8192 <= hm) -> (hm + 24 <= lst \/ lst + 8192 <= hm) ->
  rng RNG b 8192 ->
  ek_seps ek L hm lst ->
  (* [comment removed for export] *)
  dk_preC ek g RNG t lst hm (qb + ek_delta ek n) m -> dk_seps g L hm ->
  (* [comment removed for export] *)
  ADEPOT DI L m ->
  sclr (al_nodes L) 1048576 -> al_nodes L + 1048576 <= ATOP -> sclr (al_store L) 8388608 -> al_store L + 8388608 <= ATOP ->
  (t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) -> (t + 4096 <= al_store L \/ al_store L + 8388608 <= t) ->
  bv_unsigned sp < 2^47 ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 -> rng RNG hm 24 -> rng RNG (shad (hm + 16)) (shlen (rup n 8)) ->
  AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L -> iclr t 4096 ->      (* [comment removed for export] *)
  evtF asegs RNG (free_torec_post L ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n nb fst0 lst qb b1 actx lo m)
    (MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + -2272)) gp tp t0 t1 t2 (Z_to_bv 64 (t + 2128)) (Z_to_bv 64 (t + 208))
             (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 hm) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 n) (Z_to_bv 64 Q_CACHE)
             s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x382f8) fc None m (seg_rom asegs)).
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_afree_iseg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_front.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_adrain.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tail.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_icpt.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_aenqueueR.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tailR__A3W.F_afree_tailR.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tailR__A3W.F_afree_icptR.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition drain_torec_post (gfull : bool) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 : word) (F : bvmap 5 word) (fc : bv 32)
    (t nb fst lst qb gnb gfst glst gqb lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 AQUAR_Q) (Z_to_bv 64 Q_MIN) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x35b08) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (t + 80, t + 112); (0xab708, 0xab708 + 4); (0xab710, 0xab710 + 32); (glst, glst + 8)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (t + 80) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells asegs m' 0xab708 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ rw_cells asegs m' 0xab710 [C8 (Z_to_bv 64 (gnb + nb)); C8 (Z_to_bv 64 (if gfull then gfst else fst)); C8 (Z_to_bv 64 lst);
                                   C8 (Z_to_bv 64 (gqb + qb))]
    /\ (if gfull then rw_cells asegs m' glst [C8 (Z_to_bv 64 fst)] else True).

Definition drain_torec_stmt : Prop := forall (gfull : bool) (t glst : Z) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (nb fst lst qb gnb gfst gqb gnx lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 AQUAR_Q -> a1 = Z_to_bv 64 (t + 80) ->
  rw_cells asegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 < nb < 2^63 -> 0 <= qb -> 0 <= fst < 2^64 -> 0 <= lst < 2^64 ->
  rw_cells asegs m AQ_MUTEX [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m AQ_GCACHE [C8 (Z_to_bv 64 gnb); C8 (Z_to_bv 64 gfst); C8 (Z_to_bv 64 glst); C8 (Z_to_bv 64 gqb)] ->
  0 <= gnb < 2^62 -> 0 <= gqb -> Q_MAX < gqb + qb -> gqb + qb < 2^63 -> 0 <= gfst < 2^64 -> 0 <= glst < 2^64 ->
  rw_cells asegs m AQ_MAX [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->
  (if gfull then 0 < gnb /\ rw_cells asegs m glst [C8 (Z_to_bv 64 gnx)] /\ AIMG_HI <= glst /\ glst + Q_BATCH_BYTES <= ATOP
                 /\ (t + 4096 <= glst \/ glst + Q_BATCH_BYTES <= t)
   else gnb = 0) ->
  iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 -> (if gfull then rng RNG glst Q_BATCH_BYTES else True) ->
  evtF asegs RNG (drain_torec_post gfull ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 F fc t nb fst lst qb gnb gfst glst gqb lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x35964) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dk_preC (ek : enq_kind) (g : gqd) (RNG : footprint) (t lst hm qb' : Z) (m : amem) : Prop :=
     g_drain g = true
  /\ rw_cells asegs m 0xab708 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
  /\ rw_cells asegs m 0xab710 [C8 (Z_to_bv 64 (g_nb g)); C8 (Z_to_bv 64 (g_fst g)); C8 (Z_to_bv 64 (g_lst g)); C8 (Z_to_bv 64 (g_qb g))]
  /\ 0 <= g_nb g < 2^62 /\ 0 <= g_qb g /\ 0 <= g_fst g < 2^64 /\ 0 <= g_lst g < 2^64
  /\ Q_CACHE < qb' /\ Q_MAX < g_qb g + qb' /\ g_qb g + qb' < 2^63
  /\ (if g_full g then 0 < g_nb g /\ rw_cells asegs m (g_lst g) [C8 (Z_to_bv 64 (g_nx g))] /\ 0x10007fff8000 <= g_lst g /\ g_lst g + 8192 <= ATOP
                     /\ (t + 4096 <= g_lst g \/ g_lst g + 8192 <= t) /\ (hm + 16 <= g_lst g \/ g_lst g + 8 <= hm)
                     /\ (lst + 8192 <= g_lst g \/ g_lst g + 8192 <= lst) /\ (ek_b ek lst + 8192 <= g_lst g \/ g_lst g + 8192 <= ek_b ek lst)
                     /\ rng RNG (g_lst g) 8192
      else g_nb g = 0 /\ g_lst g = 0).

Definition dk_postC (g : gqd) (nb' fst' lst' qb' : Z) (m' : amem) : Prop :=
     rw_cells asegs m' 0xab708 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
  /\ rw_cells asegs m' 0xab710 [C8 (Z_to_bv 64 (g_nb g + nb')); C8 (Z_to_bv 64 (if g_full g then g_fst g else fst'));
                                 C8 (Z_to_bv 64 lst'); C8 (Z_to_bv 64 (g_qb g + qb'))]
  /\ (if g_full g then rw_cells asegs m' (g_lst g) [C8 (Z_to_bv 64 fst')] else True).

(* [comment removed for export] *)
Definition put_frame (cbc cbs s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
  [C8 cbc; C8 cbs; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition put_torec_post (ek : enq_kind) (g : gqd)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 : word) (F : bvmap 5 word) (fc : bv 32)
    (t hm n nb fst0 lst qb b1 actx lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 xs0 xs1 xs2 xs3 xs4 xs5 xs6 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR (Z_to_bv 64 0x38138) (Z_to_bv 64 (bv_unsigned sp - 80)) gp tp t0 t1 t2 xs0 xs1
                  (Z_to_bv 64 AQUAR_Q) (Z_to_bv 64 Q_MIN) (Z_to_bv 64 (t + 208)) a3 a4 a5 a6 a7 xs2 xs3 xs4 xs5 xs6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x35b08) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 144, bv_unsigned sp); (shad (hm + 16), shad (hm + 16) + shlen (rup n 8));
              (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792);
              (lst, lst + qsz lst); (ek_b ek lst, ek_b ek lst + 8192);
              (0xab708, 0xab708 + 4); (0xab710, 0xab710 + 32); (dk_glst g lst, dk_glst g lst + 8)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp - 80)
    /\ rw_cells asegs m' (bv_unsigned sp - 80) (put_frame (Z_to_bv 64 (t + 208)) a3 s6 s5 s4 s3 s2 s1 s0 ra)
    /\ rw_cells asegs m' (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) (repeat (Z_to_bv 8 253) (Z.to_nat (shlen (rup n 8))))]
    /\ rw_cells asegs m' hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)]
    /\ rw_cells asegs m' (t + 80) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ ek_post ek t lst hm n m'
    /\ dk_postC g (ek_nb ek nb) (ek_fst ek fst0) (ek_lst ek lst) (qb + ek_delta ek n) m'.

(* [comment removed for export] *)
Definition put_torec_stmt : Prop := forall (ek : enq_kind) (g : gqd) (t hm lst : Z) RNG
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n nb fst0 qb b1 actx lo : Z) (sjunk : list byte),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 144 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 0xab670 -> a1 = Z_to_bv 64 (t + 80) -> a2 = Z_to_bv 64 (t + 208) -> a4 = Z_to_bv 64 hm -> a5 = Z_to_bv 64 n ->
  rw_cells asegs m 0xab6b0 [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->
  rw_cells asegs m 0xa5888 [C8 (Z_to_bv 64 AFLAGS)] ->
  rw_cells asegs m 0xac224 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->
  poison_cells m ->
  rw_cells asegs m hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  1 <= n <= Q_MAX -> 0 <= b1 < 256 -> hm mod 16 = 0 -> ablk hm (hm + 16 + rup n 8) -> tclr hm 24 -> hm + 16 + rup n 8 <= ATOP -> hm + 16 <= ATOP ->
  rw_cells asegs m (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) sjunk] ->
  rw_cells asegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= qb -> qb + n + 8192 < 2^62 -> 0 <= fst0 < 2^64 -> 0 <= lst < 2^64 ->
  sclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> t mod 4096 = 0 -> (hm + 16 <= t \/ t + 4096 <= hm) ->
  ek_pre ek RNG t nb lst n hm m ->
  dk_preC ek g RNG t lst hm (qb + ek_delta ek n) m ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 -> rng RNG hm 16 -> rng RNG (shad (hm + 16)) (shlen (rup n 8)) ->
  iclr t 4096 ->                                            (* [comment removed for export] *)
  evtF asegs RNG (put_torec_post ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 F fc t hm n nb fst0 lst qb b1 actx lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3805c) fc None m (seg_rom asegs)).


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition put_from_refill_torec_stmt : Prop := forall (full : bool) (g : gqd) (t hm lst b : Z) RNG
    (ra sp gp tp s0 s1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (ra0 t0 t1 t2 a1 a2' a3' a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : amem) (n nb fst0 qb b1 actx lo nx bsz cnt spacebeg : Z) (maxc csz stj idxw : word) (chunks hs : list word)
    (j0 : list byte),
  let ek := EkNew full nx bsz cnt maxc csz stj idxw chunks spacebeg b hs in
  stk asegs m lo (bv_unsigned sp + -144) -> ATOP <= lo -> lo <= bv_unsigned sp - 144 ->
  mem_inv asegs m ->
  a2 = Z_to_bv 64 (t + 208) ->
  (* [comment removed for export] *)
  rw_cells asegs m (bv_unsigned sp + -80) [C8 a2; C8 a3; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m (bv_unsigned sp + -144)
     [CB 8 j0; C8 (Z_to_bv 64 hm); C8 a2; C8 a3; C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 (t + 80)); C8 (Z_to_bv 64 0xab670); C8 (Z_to_bv 64 0x38200)] ->
  (* [comment removed for export] *)
  rw_cells asegs m 0xab6b0 [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->
  (* [comment removed for export] *)
  rw_cells asegs m hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  1 <= n <= Q_MAX -> hm mod 16 = 0 -> ablk hm (hm + 16 + rup n 8) -> tclr hm 24 -> hm + 16 + rup n 8 <= ATOP -> hm + 16 <= ATOP ->
  rw_cells asegs m (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) (repeat (Z_to_bv 8 253) (Z.to_nat (shlen (rup n 8))))] ->
  (* [comment removed for export] *)
  rw_cells asegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= qb -> qb + n + 8192 < 2^62 -> 0 <= fst0 < 2^64 -> 0 <= lst < 2^64 ->
  sclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> t mod 4096 = 0 -> (hm + 16 <= t \/ t + 4096 <= hm) ->
  (* [comment removed for export] *)
  (if full then 0 < nb /\ rw_cells asegs m lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)]
             /\ 0 <= nx < 2^64 /\ 0 <= bsz < 2^64 /\ 0x10007fff8000 <= lst /\ lst + 8192 <= ATOP
             /\ u64arr asegs m (lst + 24) hs /\ length hs = 1021%nat
             /\ rng RNG lst 8192
   else nb = 0 /\ lst = 0) ->
  rw_cells asegs m 0xab3b8 [C8 (Z_to_bv 64 spacebeg)] ->
  rw_cells asegs m (t + 2128) [C4 (Z_to_bv 64 cnt); C4 maxc; C8 csz] ->
  u32arr asegs m (t + 2128 + 16) chunks -> length chunks = 16%nat ->
  0 < cnt <= 16 -> nth_error chunks (Z.to_nat (cnt - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
  rw_cells asegs m (t + 2784) [C8 stj] ->
  b = spacebeg + 24 * 2^32 + 16 * bv_unsigned idxw ->
  (exists bs, rw_cells asegs m b [CB (Z.to_nat 8192) bs]) ->
  0 < spacebeg -> 0x10007fff8000 <= b -> b + 8192 <= ATOP ->
  (t + 4096 <= b \/ b + 8192 <= t) -> (t + 4096 <= lst \/ lst + 8192 <= t \/ lst = 0) -> (b + 8192 <= lst \/ lst + 8192 <= b) ->
  (hm + 16 <= b \/ b + 8192 <= hm) -> (hm + 16 <= lst \/ lst + 8192 <= hm) ->
  rng RNG b 8192 ->
  (* [comment removed for export] *)
  dk_preC ek g RNG t lst hm (qb + ek_delta ek n) m ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 -> rng RNG hm 16 -> rng RNG (shad (hm + 16)) (shlen (rup n 8)) ->
  iclr t 4096 ->                                            (* [comment removed for export] *)
  evtF asegs RNG (put_torec_post ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 F fc t hm n nb fst0 lst qb b1 actx lo m)
    (MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 (Z_to_bv 64 (t + 2128)) (Z_to_bv 64 (t + 208))
             (Z_to_bv 64 1) a1 a2' a3' a4 a5 a6 a7
             (Z_to_bv 64 hm) (Z_to_bv 64 (t + 80)) a3 (Z_to_bv 64 n) (Z_to_bv 64 Q_CACHE) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x38360) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithDepot.
Variable DI : ADepotIface.

(* [comment removed for export] *)
Definition free_torec_post (L : alayout) (ek : enq_kind) (g : gqd)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t hm n nb fst0 lst qb b1 actx lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (id : Z) (t0 t1 t2 xs0 xs1 xs2 xs3 xs4 xs5 xs6 ps0 ps1 ps2 ps3 ps4 ps5 spv a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m' (sj' : list word)
                    (csA csT : list cell) (junk2 : list byte),
    let spP := bv_unsigned sp - 2128 in
    ms' = MS (mkR (Z_to_bv 64 0x38138) (Z_to_bv 64 (spP - 80)) gp tp t0 t1 t2 xs0 xs1
                  (Z_to_bv 64 AQUAR_Q) (Z_to_bv 64 Q_MIN) (Z_to_bv 64 (t + 208)) a3 a4 a5 a6 a7 xs2 xs3 xs4 xs5 xs6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x35b08) fc None m' (seg_rom asegs)
    /\ munch ([(bv_unsigned sp - 4096, bv_unsigned sp); (0xafc00, 0xafc00 + 0x81030); (0x13e488, 0x13e488 + 4);
               (t + 3168, t + 3169); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368);
               (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608);
               (shad (hm + 16), shad (hm + 16) + shlen (rup n 8)); (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792);
               (lst, lst + qsz lst); (ek_b ek lst, ek_b ek lst + 8192);
               (0xab708, 0xab708 + 4); (0xab710, 0xab710 + 32); (dk_glst g lst, dk_glst g lst + 8)]%Z) m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (spP - 80)
    /\ 0 < id < 2^31
    (* [comment removed for export] *)
    /\ rw_cells asegs m' (spP - 80) (put_frame (Z_to_bv 64 (t + 208)) a3 s6 ps5 ps4 ps3 ps2 ps1 ps0 (Z_to_bv 64 353172))
    (* [comment removed for export] *)
    /\ rw_cells asegs m' spP csA /\ cells_size csA = 16%nat
    /\ rw_cells asegs m' (spP + 16) csT /\ cells_size csT = 2040%nat
    /\ rw_cells asegs m' (bv_unsigned sp - 72) [C8 spv; CB 8 junk2; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)]
    /\ rw_cells asegs m' (hm + 16) [C8 (Z_to_bv 64 id)]
    /\ rw_cells asegs m' (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) (repeat (Z_to_bv 8 253) (Z.to_nat (shlen (rup n 8))))]
    /\ rw_cells asegs m' (t + 80) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ ek_post ek t lst hm n m'
    /\ dk_postC g (ek_nb ek nb) (ek_fst ek fst0) (ek_lst ek lst) (qb + ek_delta ek n) m'
    /\ u64arr asegs m' (t + 2800) sj' /\ length sj' = 46%nat
    /\ rw_cells asegs m' (t + 3168) [C1 (Z_to_bv 8 0)]
    /\ rw_cells asegs m' 0x13e488 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ stk asegs m' 0xafc00 (0xafc00 + 0x81030)
    /\ (forall j, 0 <= j < 32768 -> bytes_at asegs m' (0xafc08 + 8 * j) (le8 (Z_to_bv 64 0)))
    /\ ADEPOT DI L m'.

(* [comment removed for export] *)
Definition free_torec_stmt : Prop := forall (L : alayout) (ia : bool) (ek : enq_kind) (g : gqd) RNG
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem)
    (t ctx hm n b1 actx lo top bot nb fst0 lst qb : Z) (uw : word) (sj : list word) (sjunk : list byte) (trt : list Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 (hm + 16) ->
  bv_unsigned sp mod 16 = 0 ->
  allocA_cells m ctx t -> poison_cells m ->
  rw_cells asegs m 0xaf6fc [C4 (Z_to_bv 64 30)] ->
  rw_cells asegs m 0x14054a [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m 0xa5870 [C8 (Z_to_bv 64 0x13e4a0)] -> rw_cells asegs m 0x13e4a0 [C8 (Z_to_bv 64 4096)] ->
  rw_cells asegs m 0x1404c8 [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m 0xab6b0 [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->
  rw_cells asegs m 0xa5888 [C8 (Z_to_bv 64 AFLAGS)] ->
  rw_cells asegs m 0xac224 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->
  rw_cells asegs m 0x13e488 [C1 (Z_to_bv 8 (if ia then 1 else 0)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  stk asegs m 0xafc00 (0xafc00 + 0x81030) ->
  (ia = true -> forall j, 0 <= j < 32768 -> bytes_at asegs m (0xafc08 + 8 * j) (le8 (Z_to_bv 64 0))) ->
  rw_cells asegs m (ctx + 8) [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m t [C8 (Z_to_bv 64 ctx); C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)] ->
  rw_cells asegs m (t + 40) [C1 (Z_to_bv 8 0)] -> rw_cells asegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  rw_cells asegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= qb -> qb + n + 8192 < 2^62 -> 0 <= fst0 < 2^64 -> 0 <= lst < 2^64 ->
  0 < ctx -> sclr ctx 65536 -> ctx + 4096 <= ATOP ->
  sclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> t mod 4096 = 0 -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  rw_cells asegs m hm [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  rw_cells asegs m (hm + 16) [C8 uw] -> 0 <= b1 < 256 -> Z.land b1 3 = 1 -> 1 <= n <= Q_MAX -> hm mod 16 = 0 ->
  ablk hm (hm + 16 + rup n 8) -> tclr hm 24 -> hm + 16 + rup n 8 <= ATOP -> hm + 24 <= ATOP ->
  rw_cells asegs m (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) sjunk] ->
  (hm + 24 <= t \/ t + 4096 <= hm) -> (hm + 24 <= ctx \/ ctx + 4096 <= hm) ->
  ek_pre ek RNG t nb lst n hm m -> ek_seps ek L hm lst ->
  dk_preC ek g RNG t lst hm (qb + ek_delta ek n) m -> dk_seps g L hm ->
  ADEPOT DI L m ->
  sclr (al_nodes L) 1048576 -> al_nodes L + 1048576 <= ATOP -> sclr (al_store L) 8388608 -> al_store L + 8388608 <= ATOP ->
  (hm + 24 <= al_nodes L \/ al_nodes L + 1048576 <= hm) -> (hm + 24 <= al_store L \/ al_store L + 8388608 <= hm) ->
  (t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) -> (t + 4096 <= al_store L \/ al_store L + 8388608 <= t) ->
  (ctx + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= ctx) -> (ctx + 4096 <= al_store L \/ al_store L + 8388608 <= ctx) -> tclr (al_nodes L) 1048576 -> tclr (al_store L) 8388608 ->
  afree_unw RNG lo m top sp s0 ra trt ->
  bv_unsigned s0 <> bv_unsigned sp + 8 ->
  In (AFREE_PC :: trt) (al_U L) ->
  0 <= bot -> bot < bv_unsigned sp -> bot < top -> 4096 <= top <= 2^47 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 -> rng RNG hm 24 -> rng RNG (shad (hm + 16)) (shlen (rup n 8)) ->
  AIMG_HI <= ctx -> AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L -> iclr t 4096 ->      (* [comment removed for export] *)
  evtF asegs RNG (free_torec_post L ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n nb fst0 lst qb b1 actx lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
Definition free_from_refill_torec_stmt : Prop := forall (L : alayout) (full : bool) (g : gqd) RNG
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : amem)
    (t hm n b1 actx lo nb fst0 lst qb nx bsz cnt spacebeg id b : Z) (maxc csz stj idxw : word) (sj tb chunks hs : list word)
    (junk2 j0 : list byte) (trt : list Z),
  let ek := EkNew full nx bsz cnt maxc csz stj idxw chunks spacebeg b hs in
  stk asegs m lo (bv_unsigned sp + -2272) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
  mem_inv asegs m ->
  (* [comment removed for export] *)
  rw_cells asegs m (bv_unsigned sp + -2128) [C8 (Z_to_bv 64 (bv_unsigned sp + -2128 + 16)); C4 (Z_to_bv 64 (1 + Z.of_nat (length trt))); C4 (Z_to_bv 64 0)] ->
  u64arr asegs m (bv_unsigned sp + -2128 + 16) tb -> length tb = 255%nat ->
  rw_cells asegs m (bv_unsigned sp + -72) [C8 sp; CB 8 junk2; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m (bv_unsigned sp + -2208)
     [C8 (Z_to_bv 64 (t + 208)); C8 (Z_to_bv 64 (bv_unsigned sp + -2128)); C8 s6; C8 (Z_to_bv 64 (bv_unsigned sp + -81));
      C8 (Z_to_bv 64 (bv_unsigned sp + -2128)); C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 0x56324); C8 (Z_to_bv 64 (hm + 16)); C8 sp; C8 (Z_to_bv 64 0x56394)] ->
  rw_cells asegs m (bv_unsigned sp + -2272)
     [CB 8 j0; C8 (Z_to_bv 64 hm); C8 (Z_to_bv 64 (t + 208)); C8 (Z_to_bv 64 (bv_unsigned sp + -2128)); C8 (Z_to_bv 64 n);
      C8 (Z_to_bv 64 (t + 80)); C8 (Z_to_bv 64 0xab670); C8 (Z_to_bv 64 0x38200)] ->
  (* [comment removed for export] *)
  rw_cells asegs m 0xab6b0 [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->
  (* [comment removed for export] *)
  rw_cells asegs m hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  rw_cells asegs m (hm + 16) [C8 (Z_to_bv 64 id)] -> 0 < id < 2^31 ->
  1 <= n <= Q_MAX -> hm mod 16 = 0 -> ablk hm (hm + 16 + rup n 8) -> tclr hm 24 -> hm + 16 + rup n 8 <= ATOP -> hm + 24 <= ATOP ->
  rw_cells asegs m (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) (repeat (Z_to_bv 8 253) (Z.to_nat (shlen (rup n 8))))] ->
  (* [comment removed for export] *)
  rw_cells asegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= qb -> qb + n + 8192 < 2^62 -> 0 <= fst0 < 2^64 -> 0 <= lst < 2^64 ->
  sclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> t mod 4096 = 0 -> (hm + 24 <= t \/ t + 4096 <= hm) ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat -> rw_cells asegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m 0x13e488 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  stk asegs m 0xafc00 (0xafc00 + 0x81030) ->
  (forall j, 0 <= j < 32768 -> bytes_at asegs m (0xafc08 + 8 * j) (le8 (Z_to_bv 64 0))) ->
  (* [comment removed for export] *)
  (if full then 0 < nb /\ rw_cells asegs m lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)]
             /\ 0 <= nx < 2^64 /\ 0 <= bsz < 2^64 /\ 0x10007fff8000 <= lst /\ lst + 8192 <= ATOP
             /\ u64arr asegs m (lst + 24) hs /\ length hs = 1021%nat
             /\ rng RNG lst 8192
   else nb = 0 /\ lst = 0) ->
  rw_cells asegs m 0xab3b8 [C8 (Z_to_bv 64 spacebeg)] ->
  rw_cells asegs m (t + 2128) [C4 (Z_to_bv 64 cnt); C4 maxc; C8 csz] ->
  u32arr asegs m (t + 2128 + 16) chunks -> length chunks = 16%nat ->
  0 < cnt <= 16 -> nth_error chunks (Z.to_nat (cnt - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
  rw_cells asegs m (t + 2784) [C8 stj] ->
  b = spacebeg + 24 * 2^32 + 16 * bv_unsigned idxw ->
  (exists bs, rw_cells asegs m b [CB (Z.to_nat 8192) bs]) ->
  0 < spacebeg -> 0x10007fff8000 <= b -> b + 8192 <= ATOP ->
  (t + 4096 <= b \/ b + 8192 <= t) -> (t + 4096 <= lst \/ lst + 8192 <= t \/ lst = 0) -> (b + 8192 <= lst \/ lst + 8192 <= b) ->
  (hm + 24 <= b \/ b + 8192 <= hm) -> (hm + 24 <= lst \/ lst + 8192 <= hm) ->
  rng RNG b 8192 ->
  ek_seps ek L hm lst ->
  (* [comment removed for export] *)
  dk_preC ek g RNG t lst hm (qb + ek_delta ek n) m -> dk_seps g L hm ->
  (* [comment removed for export] *)
  ADEPOT DI L m ->
  sclr (al_nodes L) 1048576 -> al_nodes L + 1048576 <= ATOP -> sclr (al_store L) 8388608 -> al_store L + 8388608 <= ATOP ->
  (t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) -> (t + 4096 <= al_store L \/ al_store L + 8388608 <= t) ->
  bv_unsigned sp < 2^47 ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 -> rng RNG hm 24 -> rng RNG (shad (hm + 16)) (shlen (rup n 8)) ->
  AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L -> iclr t 4096 ->      (* [comment removed for export] *)
  evtF asegs RNG (free_torec_post L ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n nb fst0 lst qb b1 actx lo m)
    (MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + -2272)) gp tp t0 t1 t2 (Z_to_bv 64 (t + 2128)) (Z_to_bv 64 (t + 208))
             (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 hm) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 n) (Z_to_bv 64 Q_CACHE)
             s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x38360) fc None m (seg_rom asegs)).
End WithDepot.
End CANSEC1.
End TwB.
End F_afreeC_iface.
