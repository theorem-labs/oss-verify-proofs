(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_adrain__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_aenqueue OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_adrain OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_aput.
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
Local Ltac iclr_of H := clear -H; unfold iclr, AIMG_LO, AIMG_HI in *; lia.
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


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Inductive enq_kind :=
| EkAppend (nx bsz cnt : Z) (hs : list word) (cnt24 : Z) (maxc csz stj : word)
| EkNew (full : bool) (nx bsz cnt24 : Z) (maxc csz stj idxw : word) (chunks : list word) (spacebeg b : Z) (hs : list word).

(* [comment removed for export] *)
Record gqd := mkGQ { g_drain : bool; g_full : bool; g_nb : Z; g_fst : Z; g_lst : Z; g_qb : Z; g_nx : Z }.

Definition ek_nb (ek : enq_kind) (nb : Z) : Z := match ek with EkAppend _ _ _ _ _ _ _ _ => nb | EkNew _ _ _ _ _ _ _ _ _ _ _ _ => nb + 1 end.
Definition ek_fst (ek : enq_kind) (fst0 : Z) : Z :=
  match ek with EkAppend _ _ _ _ _ _ _ _ => fst0 | EkNew full _ _ _ _ _ _ _ _ _ b _ => if full then fst0 else b end.
Definition ek_lst (ek : enq_kind) (lst : Z) : Z := match ek with EkAppend _ _ _ _ _ _ _ _ => lst | EkNew _ _ _ _ _ _ _ _ _ _ b _ => b end.
Definition ek_delta (ek : enq_kind) (n : Z) : Z := match ek with EkAppend _ _ _ _ _ _ _ _ => n | EkNew _ _ _ _ _ _ _ _ _ _ _ _ => n + 8192 end.
Definition ek_b (ek : enq_kind) (lst : Z) : Z := match ek with EkAppend _ _ _ _ _ _ _ _ => lst | EkNew _ _ _ _ _ _ _ _ _ _ b _ => b end.
Definition dk_glst (g : gqd) (lst : Z) : Z := if g_drain g then g_lst g else lst.

(* [comment removed for export] *)
Definition ek_pre (ek : enq_kind) (RNG : footprint) (t nb lst n hm : Z) (m : amem) : Prop :=
  match ek with
  | EkAppend nx bsz cnt hs cnt24 maxc csz stj =>
         0 < nb /\ rw_cells asegs m lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 cnt)]
      /\ 0 <= cnt < 1021 /\ 0 <= bsz /\ bsz + n < 2^63 /\ 0 <= nx < 2^64
      /\ u64arr asegs m (lst + 24) hs /\ length hs = Z.to_nat cnt
      /\ (exists bs, rw_cells asegs m (lst + 24 + 8 * cnt) [CB (Z.to_nat (8192 - 24 - 8 * cnt)) bs])
      /\ 0x10007fff8000 <= lst /\ lst + 8192 <= ATOP /\ (t + 4096 <= lst \/ lst + 8192 <= t) /\ (hm + 16 <= lst \/ lst + 8192 <= hm)
      /\ rw_cells asegs m (t + 2128) [C4 (Z_to_bv 64 cnt24); C4 maxc; C8 csz] /\ rw_cells asegs m (t + 2784) [C8 stj]   (* [comment removed for export] *)
      /\ rng RNG lst 8192
  | EkNew full nx bsz cnt24 maxc csz stj idxw chunks spacebeg b hs =>
         (if full then 0 < nb /\ rw_cells asegs m lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)]
                    /\ 0 <= nx < 2^64 /\ 0 <= bsz < 2^64 /\ 0x10007fff8000 <= lst /\ lst + 8192 <= ATOP
                    /\ u64arr asegs m (lst + 24) hs /\ length hs = 1021%nat    (* [comment removed for export] *)
                    /\ rng RNG lst 8192
          else nb = 0 /\ lst = 0)
      /\ rw_cells asegs m 0xaafb8 [C8 (Z_to_bv 64 spacebeg)]
      /\ rw_cells asegs m (t + 2128) [C4 (Z_to_bv 64 cnt24); C4 maxc; C8 csz]
      /\ u32arr asegs m (t + 2128 + 16) chunks /\ length chunks = 16%nat
      /\ 0 < cnt24 <= 16 /\ nth_error chunks (Z.to_nat (cnt24 - 1)) = Some idxw /\ bv_unsigned idxw < 2^32
      /\ rw_cells asegs m (t + 2784) [C8 stj]
      /\ b = spacebeg + 24 * 2^32 + 16 * bv_unsigned idxw
      /\ (exists bs, rw_cells asegs m b [CB (Z.to_nat 8192) bs])
      /\ 0 < spacebeg /\ 0x10007fff8000 <= b /\ b + 8192 <= ATOP
      /\ (t + 4096 <= b \/ b + 8192 <= t) /\ (t + 4096 <= lst \/ lst + 8192 <= t \/ lst = 0) /\ (b + 8192 <= lst \/ lst + 8192 <= b)
      /\ (hm + 16 <= b \/ b + 8192 <= hm) /\ (hm + 16 <= lst \/ lst + 8192 <= hm)
      /\ rng RNG b 8192
  end.

(* [comment removed for export] *)
Definition ek_post (ek : enq_kind) (t lst hm n : Z) (m' : amem) : Prop :=
  match ek with
  | EkAppend nx bsz cnt hs cnt24 maxc csz stj =>
         rw_cells asegs m' lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 (bsz + n)); C8 (Z_to_bv 64 (cnt + 1))]
      /\ u64arr asegs m' (lst + 24) (hs ++ [Z_to_bv 64 hm])
      /\ (exists bs, rw_cells asegs m' (lst + 24 + 8 * (cnt + 1)) [CB (Z.to_nat (8192 - 24 - 8 * (cnt + 1))) bs])
      /\ rw_cells asegs m' (t + 2128) [C4 (Z_to_bv 64 cnt24); C4 maxc; C8 csz] /\ rw_cells asegs m' (t + 2784) [C8 stj]
  | EkNew full nx bsz cnt24 maxc csz stj idxw chunks spacebeg b hs =>
         rw_cells asegs m' (t + 2128) [C4 (Z_to_bv 64 (cnt24 - 1)); C4 maxc; C8 csz]
      /\ (exists stj' : word, rw_cells asegs m' (t + 2784) [C8 stj'])
      /\ rw_cells asegs m' b [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (n + 8192)); C8 (Z_to_bv 64 1)]
      /\ u64arr asegs m' (b + 24) [Z_to_bv 64 hm]
      /\ (exists bs, rw_cells asegs m' (b + 24 + 8 * 1) [CB (Z.to_nat (8192 - 24 - 8 * 1)) bs])
      /\ (if full then rw_cells asegs m' lst [C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)] /\ u64arr asegs m' (lst + 24) hs else True)
  end.

(* [comment removed for export] *)
Definition dk_pre (ek : enq_kind) (g : gqd) (RNG : footprint) (t lst hm qb' : Z) (m : amem) : Prop :=
     rw_cells asegs m 0xab308 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
  /\ rw_cells asegs m 0xab310 [C8 (Z_to_bv 64 (g_nb g)); C8 (Z_to_bv 64 (g_fst g)); C8 (Z_to_bv 64 (g_lst g)); C8 (Z_to_bv 64 (g_qb g))]
  /\ 0 <= g_nb g < 2^62 /\ 0 <= g_qb g /\ 0 <= g_fst g < 2^64 /\ 0 <= g_lst g < 2^64
  /\ if g_drain g then
          Q_CACHE < qb' /\ g_qb g + qb' <= Q_MAX
       /\ (if g_full g then 0 < g_nb g /\ rw_cells asegs m (g_lst g) [C8 (Z_to_bv 64 (g_nx g))] /\ 0x10007fff8000 <= g_lst g /\ g_lst g + 8192 <= ATOP
                          /\ (t + 4096 <= g_lst g \/ g_lst g + 8192 <= t) /\ (hm + 16 <= g_lst g \/ g_lst g + 8 <= hm)
                          /\ (lst + 8192 <= g_lst g \/ g_lst g + 8192 <= lst) /\ (ek_b ek lst + 8192 <= g_lst g \/ g_lst g + 8192 <= ek_b ek lst)
                          /\ rng RNG (g_lst g) 8192
           else g_nb g = 0 /\ g_lst g = 0)
     else qb' <= Q_CACHE.

Definition dk_post (g : gqd) (nb' fst' lst' qb' : Z) (m' : amem) : Prop :=
     rw_cells asegs m' 0xab308 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
  /\ if g_drain g then
          rw_cells asegs m' 0xab310 [C8 (Z_to_bv 64 (g_nb g + nb')); C8 (Z_to_bv 64 (if g_full g then g_fst g else fst'));
                                C8 (Z_to_bv 64 lst'); C8 (Z_to_bv 64 (g_qb g + qb'))]
       /\ (if g_full g then rw_cells asegs m' (g_lst g) [C8 (Z_to_bv 64 fst')] else True)
     else rw_cells asegs m' 0xab310 [C8 (Z_to_bv 64 (g_nb g)); C8 (Z_to_bv 64 (g_fst g)); C8 (Z_to_bv 64 (g_lst g)); C8 (Z_to_bv 64 (g_qb g))].
(* [comment removed for export] *)
Definition tcache_post (g : gqd) (nb' fst' lst' qb' : Z) : list cell :=
  if g_drain g then [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
  else [C8 (Z_to_bv 64 nb'); C8 (Z_to_bv 64 fst'); C8 (Z_to_bv 64 lst'); C8 (Z_to_bv 64 qb')].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition put_tail_post (ek : enq_kind) (g : gqd)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t hm n nb fst0 lst qb b1 actx lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 144, bv_unsigned sp); (shad (hm + 16), shad (hm + 16) + shlen (rup n 8));
              (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792);
              (lst, lst + qsz lst); (ek_b ek lst, ek_b ek lst + 8192);      (* [comment removed for export] *)
              (0xab308, 0xab308 + 4); (0xab310, 0xab310 + 32); (dk_glst g lst, dk_glst g lst + 8)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) (repeat (Z_to_bv 8 253) (Z.to_nat (shlen (rup n 8))))]
    /\ rw_cells asegs m' hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)]
    /\ rw_cells asegs m' (t + 80) (tcache_post g (ek_nb ek nb) (ek_fst ek fst0) (ek_lst ek lst) (qb + ek_delta ek n))
    /\ ek_post ek t lst hm n m'
    /\ dk_post g (ek_nb ek nb) (ek_fst ek fst0) (ek_lst ek lst) (qb + ek_delta ek n) m'.

Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

Definition put_tail_spec__stmt : Prop := forall (ek : enq_kind) (g : gqd) (t hm lst : Z) RNG
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n nb fst0 qb b1 actx lo : Z) (sjunk : list byte),
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
  0 <= nb < 2^62 -> 0 <= qb -> qb + n + 8192 < 2^62 -> 0 <= fst0 < 2^64 -> 0 <= lst < 2^64 ->
  sclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> t mod 4096 = 0 -> (hm + 16 <= t \/ t + 4096 <= hm) ->
  ek_pre ek RNG t nb lst n hm m ->
  dk_pre ek g RNG t lst hm (qb + ek_delta ek n) m ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 -> rng RNG hm 16 -> rng RNG (shad (hm + 16)) (shlen (rup n 8)) ->
  iclr t 4096 ->                                            (* [comment removed for export] *)
  evtF asegs RNG (put_tail_post ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n nb fst0 lst qb b1 actx lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x37ff4) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable ek : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 0).
Variable g : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 1).
Variable t : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 2).
Variable hm : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 3).
Variable lst : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 4).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 5).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 6).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 7).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 8).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 9).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 10).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 11).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 12).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 13).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 14).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 15).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 16).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 17).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 18).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 19).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 20).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 21).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 22).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 23).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 24).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 25).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 26).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 27).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 28).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 29).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 30).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 31).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 32).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 33).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 34).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 35).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 36).
Variable F : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 37).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 38).
Variable m : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 39).
Variable n : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 40).
Variable nb : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 41).
Variable fst0 : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 42).
Variable qb : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 43).
Variable b1 : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 44).
Variable actx : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 45).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 46).
Variable sjunk : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 47).
#[using="Type"] Lemma put_tail_spec__body : ltac:(let T := type of (fun (h : put_tail_spec__stmt) => h ek g t hm lst RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n nb fst0 qb b1 actx lo sjunk) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (ek, (g, (t, (hm, (lst, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (n, (nb, (fst0, (qb, (b1, (actx, (lo, sjunk)))))))))))))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO MI -> -> -> -> -> QK GF FLG PC HD N B1 AL HLO TCH HHI HCE SH QC NB QB QBN FST LST T0 T1 TAL DHT EK DK RIMG RTLS RSTK RT RH RSH TI.
  band_int TI. (pose proof (ablk_lin _ _ HLO) as ndP__; nd_pre ndP__ 4%nat; intros HL1 HL2 HL3 HL4; nd_post). unfold AIMG_HI in HL1. band_int HLO. band_lin. band_int T0.   (* [comment removed for export] *)
  assert (SHB : 2148238848 <= shad (hm + 16) /\ shad (hm + 16) + shlen (rup n 8) <= 0x10007fff8000).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold Q_MAX in N. Z.div_mod_to_equations. lia. }
  assert (RUP : n <= rup n 8 <= n + 7 /\ rup n 8 mod 8 = 0) by (unfold rup; Z.div_mod_to_equations; lia).
  assert (SHL : 0 < shlen (rup n 8) < 0x10000000) by (unfold shlen; rewrite Z.shiftr_div_pow2 by lia; unfold Q_MAX in N; Z.div_mod_to_equations; lia).
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (shad (hm + 16), shad (hm + 16) + shlen (rup n 8));
              (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792);
              (lst, lst + qsz lst); (ek_b ek lst, ek_b ek lst + 8192);      (* [comment removed for export] *)
              (0xab308, 0xab308 + 4); (0xab310, 0xab310 + 32); (dk_glst g lst, dk_glst g lst + 8)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  (nd_pre PC 7%nat; intros P1 P2 P3 P4 P5 P6 P7; nd_post).
  pose proof QK as QK0. rw_split QK0 1%nat QMX QK2. clear QK2.
  box DHT.
  (* [comment removed for export] *)
  destruct ek as [nx bsz cnt hs cnt24' maxc' csz' stj' | full nx bsz cnt24 maxc csz stj idxw chunks spacebeg b hs0];
  [ (nd_pre EK 16%nat; intros NB1 LB CNT BSZ BSZN NX LA LEN [junkt LJ] L0 L1 DTL DHL CR' STS' RL; nd_post); box DTL; box DHL
  | (nd_pre EK 20%nat; intros FULL SB CR CH LCH CNT NTH IXS STS HB [junkb BJ] SBP B0 BL1 DTB DTL DBL DHB DHL RB; nd_post);
    box DTB; box DTL; box DBL; box DHB; box DHL;
    destruct full; [(nd_pre FULL 9%nat; intros NB1 LB NX BSZ L0 L1 LA0 LEN0 RL; nd_post); assert (LEN0Z : Z.of_nat (length hs0) = 1021) by (rewrite LEN0; reflexivity); box LEN0 | destruct FULL as [NB0 LST0]] ];
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
    box HD. box SH'. box GLB. box CR'. box STS'.
    snapshot [(bv_unsigned sp + -80 - 64, bv_unsigned sp + -80); (t + 80 + 24, t + 80 + 32); (lst + 8, lst + 24); (lst + 24 + 8 * cnt, lst + 24 + 8 * cnt + 8)]%Z MUe WMe.
    box LJ. box LB. box QC. box LA.   (* [comment removed for export] *)
    box ST.
    call_sp (enqueue_append_spec (t + 80) lst cnt RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz lo hs);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| reflexivity| unboxed QC| lia| lia| unfold Q_MAX in *; lia| lia| lia| lia
      | unboxed LB| exact CNT| lia| unfold Q_MAX in *; lia| lia| unboxed LA| exact LEN| exists junkt; unboxed LJ
      | iclr_of TI| atop_facts; lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia|].
    try clear ST.
    clear LJ LB QC LA.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ylia). carry SH' MUe WMe ltac:(lia). carry GLB MUe WMe ltac:(ub G5; ub G7; ylia). carry CR' MUe WMe ltac:(ub DTL; ylia). carry STS' MUe WMe ltac:(ub DTL; ylia). clear MUe WMe.
    rename POST into LJ'. rename PC1 into LB'. rename PC2 into LA'. rename PC0 into QC'. destruct LJ' as [junkt' LJ'].
    (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].   (* [comment removed for export] *)
    step. step. step. step.                    (* [comment removed for export] *)
    box HD.  box LB'. box LA'. box LJ'. box CR'. box STS'.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0xab308, 0xab308 + 4); (0xab310, 0xab310 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GLB. box GC. box MX.   (* [comment removed for export] *)
    box ST.
    step. call_sp (drain_norecycle_spec true t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 lst (qb + n) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| lia| lia
      | exact QMX| split; [lia|]; split; [unboxed GLB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try lia; ub G5; ylia| exact TI| atop_facts; lia|].
    try clear ST.
    clear QC' GLB GC MX.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT; ub G6; ylia). carry LB' MUd WMd ltac:(ub DTL; first [ub G7 | pose proof GLST0]; ylia). carry LA' MUd WMd ltac:(rewrite length_app, LEN; cbn [length]; ub DTL; first [ub G7 | pose proof GLST0]; ylia). carry LJ' MUd WMd ltac:(ub DTL; first [ub G7 | pose proof GLST0]; ylia). carry CR' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; ylia). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; ylia). clear MUd WMd.
    do 10 step.
    release_frame FRP ST (bv_unsigned sp).
    unfold put_tail_post. rewrite ?QZE. unfold tcache_post, dk_post, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).   (* [comment removed for export] *)  all: try (eexists; eassumption).
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
    box HD. box SH'. box CR'. box STS'.
    snapshot [(bv_unsigned sp + -80 - 64, bv_unsigned sp + -80); (t + 80 + 24, t + 80 + 32); (lst + 8, lst + 24); (lst + 24 + 8 * cnt, lst + 24 + 8 * cnt + 8)]%Z MUe WMe.
    box LJ. box LB. box QC. box LA.   (* [comment removed for export] *)
    box ST.
    call_sp (enqueue_append_spec (t + 80) lst cnt RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz lo hs);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| reflexivity| unboxed QC| lia| lia| unfold Q_MAX in *; lia| lia| lia| lia
      | unboxed LB| exact CNT| lia| unfold Q_MAX in *; lia| lia| unboxed LA| exact LEN| exists junkt; unboxed LJ
      | iclr_of TI| atop_facts; lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia|].
    try clear ST.
    clear LJ LB QC LA.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ylia). carry SH' MUe WMe ltac:(lia). carry CR' MUe WMe ltac:(ub DTL; ylia). carry STS' MUe WMe ltac:(ub DTL; ylia). clear MUe WMe.
    rename POST into LJ'. rename PC1 into LB'. rename PC2 into LA'. rename PC0 into QC'. destruct LJ' as [junkt' LJ'].
    (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].   (* [comment removed for export] *)
    step. step. step. step.                    (* [comment removed for export] *)
    box HD.  box LB'. box LA'. box LJ'. box CR'. box STS'.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0xab308, 0xab308 + 4); (0xab310, 0xab310 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GC. box MX.   (* [comment removed for export] *)
    box ST.
    step. call_sp (drain_norecycle_spec false t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 lst (qb + n) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| lia| lia
      | exact QMX| exact GNB0| exact TI| atop_facts; lia| exact I|].
    try clear ST.
    clear QC' GC MX.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT;  ylia). carry LB' MUd WMd ltac:(ub DTL; first [ub G7 | pose proof GLST0]; ylia). carry LA' MUd WMd ltac:(rewrite length_app, LEN; cbn [length]; ub DTL; first [ub G7 | pose proof GLST0]; ylia). carry LJ' MUd WMd ltac:(ub DTL; first [ub G7 | pose proof GLST0]; ylia). carry CR' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; ylia). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; ylia). clear MUd WMd.
    do 10 step.
    release_frame FRP ST (bv_unsigned sp).
    unfold put_tail_post. rewrite ?QZE. unfold tcache_post, dk_post, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).   (* [comment removed for export] *)  all: try (eexists; eassumption).
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
    box HD. box SH'. box CR'. box STS'.
    snapshot [(bv_unsigned sp + -80 - 64, bv_unsigned sp + -80); (t + 80 + 24, t + 80 + 32); (lst + 8, lst + 24); (lst + 24 + 8 * cnt, lst + 24 + 8 * cnt + 8)]%Z MUe WMe.
    box LJ. box LB. box QC. box LA.   (* [comment removed for export] *)
    box ST.
    call_sp (enqueue_append_spec (t + 80) lst cnt RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz lo hs);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| reflexivity| unboxed QC| lia| lia| unfold Q_MAX in *; lia| lia| lia| lia
      | unboxed LB| exact CNT| lia| unfold Q_MAX in *; lia| lia| unboxed LA| exact LEN| exists junkt; unboxed LJ
      | iclr_of TI| atop_facts; lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia|].
    try clear ST.
    clear LJ LB QC LA.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ylia). carry SH' MUe WMe ltac:(lia). carry CR' MUe WMe ltac:(ub DTL; ylia). carry STS' MUe WMe ltac:(ub DTL; ylia). clear MUe WMe.
    rename POST into LJ'. rename PC1 into LB'. rename PC2 into LA'. rename PC0 into QC'. destruct LJ' as [junkt' LJ'].
    (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. if_cases KD; zify_cond KD; [exfalso; unfold Q_CACHE in *; lia|].   (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    do 10 step.
    release_frame FRP ST (bv_unsigned sp).
    unfold put_tail_post. rewrite ?QZE. unfold tcache_post, dk_post, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).   (* [comment removed for export] *)  all: try (eexists; eassumption).
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
    box HD. box CH. box SH'. box GLB. box LA0.
    snapshot [(bv_unsigned sp + -80 - 64, bv_unsigned sp + -80); (t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box LB. box QC.   (* [comment removed for export] *)
    box ST.
    call_sp (enqueue_new_spec true t lst b RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt24 spacebeg lo maxc csz stj idxw chunks);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| reflexivity| reflexivity| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | split; [lia|]; split; [unboxed LB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try assumption; lia
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia|].
    try clear ST.
    clear BJ STS CR LB QC.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; ylia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; ylia). carry SH' MUe WMe ltac:(lia). carry LA0 MUe WMe ltac:(rewrite LEN0Z; ub DTL; ub DBL; ylia). carry GLB MUe WMe ltac:(ub G5; ub G7; ub G8; ylia). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].
    (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].   (* [comment removed for export] *)
    step. step. step. step.                    (* [comment removed for export] *)
    box HD.  box PC3. box PC4. box PC5. box POST. box PC1. box STS'. box LA0.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0xab308, 0xab308 + 4); (0xab310, 0xab310 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GLB. box GC. box MX. box CH.   (* [comment removed for export] *)
    box ST.
    step. call_sp (drain_norecycle_spec true t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (nb + 1) fst0 b (qb + (n + 8192)) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| lia| lia
      | exact QMX| split; [lia|]; split; [unboxed GLB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try lia; ub G5; ylia| exact TI| atop_facts; lia|].
    try clear ST.
    clear QC' GLB GC MX CH.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT; ub G6; ylia). carry PC3 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; ylia). carry PC4 MUd WMd ltac:(cbn [length]; ub DTB; first [ub G8 | pose proof GLST0]; ylia). carry PC5 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; ylia). carry POST MUd WMd ltac:(ub DTL; first [ub G7 | pose proof GLST0]; ylia). carry PC1 MUd WMd ltac:(first [ub G5 | pose proof GLST0]; ylia). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; ylia). carry LA0 MUd WMd ltac:(rewrite LEN0Z; ub DTL; first [ub G7 | pose proof GLST0]; ylia). clear MUd WMd.
    do 10 step.
    release_frame FRP ST (bv_unsigned sp).
    unfold put_tail_post. rewrite ?QZE. unfold tcache_post, dk_post, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).   (* [comment removed for export] *)  all: try (eexists; eassumption).
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
    box HD. box CH. box SH'. box LA0.
    snapshot [(bv_unsigned sp + -80 - 64, bv_unsigned sp + -80); (t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box LB. box QC.   (* [comment removed for export] *)
    box ST.
    call_sp (enqueue_new_spec true t lst b RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt24 spacebeg lo maxc csz stj idxw chunks);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| reflexivity| reflexivity| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | split; [lia|]; split; [unboxed LB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try assumption; lia
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia|].
    try clear ST.
    clear BJ STS CR LB QC.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; ylia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; ylia). carry SH' MUe WMe ltac:(lia). carry LA0 MUe WMe ltac:(rewrite LEN0Z; ub DTL; ub DBL; ylia). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].
    (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].   (* [comment removed for export] *)
    step. step. step. step.                    (* [comment removed for export] *)
    box HD.  box PC3. box PC4. box PC5. box POST. box PC1. box STS'. box LA0.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0xab308, 0xab308 + 4); (0xab310, 0xab310 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GC. box MX.   (* [comment removed for export] *)
    box ST.
    step. call_sp (drain_norecycle_spec false t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (nb + 1) fst0 b (qb + (n + 8192)) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| lia| lia
      | exact QMX| exact GNB0| exact TI| atop_facts; lia| exact I|].
    try clear ST.
    clear QC' GC MX.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT;  ylia). carry PC3 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; ylia). carry PC4 MUd WMd ltac:(cbn [length]; ub DTB; first [ub G8 | pose proof GLST0]; ylia). carry PC5 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; ylia). carry POST MUd WMd ltac:(ub DTL; first [ub G7 | pose proof GLST0]; ylia). carry PC1 MUd WMd ltac:(first [ub G5 | pose proof GLST0]; ylia). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; ylia). carry LA0 MUd WMd ltac:(rewrite LEN0Z; ub DTL; first [ub G7 | pose proof GLST0]; ylia). clear MUd WMd.
    do 10 step.
    release_frame FRP ST (bv_unsigned sp).
    unfold put_tail_post. rewrite ?QZE. unfold tcache_post, dk_post, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).   (* [comment removed for export] *)  all: try (eexists; eassumption).
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
    box HD. box CH. box SH'. box LA0.
    snapshot [(bv_unsigned sp + -80 - 64, bv_unsigned sp + -80); (t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box LB. box QC.   (* [comment removed for export] *)
    box ST.
    call_sp (enqueue_new_spec true t lst b RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt24 spacebeg lo maxc csz stj idxw chunks);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| reflexivity| reflexivity| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | split; [lia|]; split; [unboxed LB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try assumption; lia
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia|].
    try clear ST.
    clear BJ STS CR LB QC.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; ylia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; ylia). carry SH' MUe WMe ltac:(lia). carry LA0 MUe WMe ltac:(rewrite LEN0Z; ub DTL; ub DBL; ylia). clear MUe WMe.
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
    box HD. box CH. box SH'. box GLB.
    snapshot [(bv_unsigned sp + -80 - 64, bv_unsigned sp + -80); (t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box QC.   (* [comment removed for export] *)
    box ST.
    call_sp (enqueue_new_spec false t lst b RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt24 spacebeg lo maxc csz stj idxw chunks);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| reflexivity| reflexivity| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | exact NB0
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia| exact I|].
    try clear ST.
    clear BJ STS CR QC.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; ylia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; ylia). carry SH' MUe WMe ltac:(lia). carry GLB MUe WMe ltac:(ub G5; ub G7; ub G8; ylia). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].
    (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].   (* [comment removed for export] *)
    step. step. step. step.                    (* [comment removed for export] *)
    box HD.  box PC3. box PC4. box PC5. box PC1. box STS'.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0xab308, 0xab308 + 4); (0xab310, 0xab310 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GLB. box GC. box MX. box CH.   (* [comment removed for export] *)
    box ST.
    step. call_sp (drain_norecycle_spec true t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (nb + 1) b b (qb + (n + 8192)) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| lia| lia
      | exact QMX| split; [lia|]; split; [unboxed GLB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try lia; ub G5; ylia| exact TI| atop_facts; lia|].
    try clear ST.
    clear QC' GLB GC MX CH.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT; ub G6; ylia). carry PC3 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; ylia). carry PC4 MUd WMd ltac:(cbn [length]; ub DTB; first [ub G8 | pose proof GLST0]; ylia). carry PC5 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; ylia). carry PC1 MUd WMd ltac:(first [ub G5 | pose proof GLST0]; ylia). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; ylia). clear MUd WMd.
    do 10 step.
    release_frame FRP ST (bv_unsigned sp).
    unfold put_tail_post. rewrite ?QZE. unfold tcache_post, dk_post, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).   (* [comment removed for export] *)  all: try (eexists; eassumption).
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
    box HD. box CH. box SH'.
    snapshot [(bv_unsigned sp + -80 - 64, bv_unsigned sp + -80); (t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box QC.   (* [comment removed for export] *)
    box ST.
    call_sp (enqueue_new_spec false t lst b RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt24 spacebeg lo maxc csz stj idxw chunks);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| reflexivity| reflexivity| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | exact NB0
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia| exact I|].
    try clear ST.
    clear BJ STS CR QC.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; ylia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; ylia). carry SH' MUe WMe ltac:(lia). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].
    (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].   (* [comment removed for export] *)
    step. step. step. step.                    (* [comment removed for export] *)
    box HD.  box PC3. box PC4. box PC5. box PC1. box STS'.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0xab308, 0xab308 + 4); (0xab310, 0xab310 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GC. box MX.   (* [comment removed for export] *)
    box ST.
    step. call_sp (drain_norecycle_spec false t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (nb + 1) b b (qb + (n + 8192)) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| lia| lia
      | exact QMX| exact GNB0| exact TI| atop_facts; lia| exact I|].
    try clear ST.
    clear QC' GC MX.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT;  ylia). carry PC3 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; ylia). carry PC4 MUd WMd ltac:(cbn [length]; ub DTB; first [ub G8 | pose proof GLST0]; ylia). carry PC5 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; ylia). carry PC1 MUd WMd ltac:(first [ub G5 | pose proof GLST0]; ylia). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; ylia). clear MUd WMd.
    do 10 step.
    release_frame FRP ST (bv_unsigned sp).
    unfold put_tail_post. rewrite ?QZE. unfold tcache_post, dk_post, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).   (* [comment removed for export] *)  all: try (eexists; eassumption).
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
    box HD. box CH. box SH'.
    snapshot [(bv_unsigned sp + -80 - 64, bv_unsigned sp + -80); (t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box QC.   (* [comment removed for export] *)
    box ST.
    call_sp (enqueue_new_spec false t lst b RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt24 spacebeg lo maxc csz stj idxw chunks);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| reflexivity| reflexivity| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | exact NB0
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia| exact I|].
    try clear ST.
    clear BJ STS CR QC.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; ylia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; ylia). carry SH' MUe WMe ltac:(lia). clear MUe WMe.
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
End Zd1.
#[using="Type"] Lemma put_tail_spec : ltac:(let t := eval cbv delta [put_tail_spec__stmt] in put_tail_spec__stmt in exact t).
Proof. exact put_tail_spec__body. Qed.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_aenqueue.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_adrain.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_aput.TwB.
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
Local Ltac iclr_of H := clear -H; unfold iclr, AIMG_LO, AIMG_HI in *; lia.
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


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Inductive enq_kind :=
| EkAppend (nx bsz cnt : Z) (hs : list word) (cnt24 : Z) (maxc csz stj : word)
| EkNew (full : bool) (nx bsz cnt24 : Z) (maxc csz stj idxw : word) (chunks : list word) (spacebeg b : Z) (hs : list word).

(* [comment removed for export] *)
Record gqd := mkGQ { g_drain : bool; g_full : bool; g_nb : Z; g_fst : Z; g_lst : Z; g_qb : Z; g_nx : Z }.

Definition ek_nb (ek : enq_kind) (nb : Z) : Z := match ek with EkAppend _ _ _ _ _ _ _ _ => nb | EkNew _ _ _ _ _ _ _ _ _ _ _ _ => nb + 1 end.
Definition ek_fst (ek : enq_kind) (fst0 : Z) : Z :=
  match ek with EkAppend _ _ _ _ _ _ _ _ => fst0 | EkNew full _ _ _ _ _ _ _ _ _ b _ => if full then fst0 else b end.
Definition ek_lst (ek : enq_kind) (lst : Z) : Z := match ek with EkAppend _ _ _ _ _ _ _ _ => lst | EkNew _ _ _ _ _ _ _ _ _ _ b _ => b end.
Definition ek_delta (ek : enq_kind) (n : Z) : Z := match ek with EkAppend _ _ _ _ _ _ _ _ => n | EkNew _ _ _ _ _ _ _ _ _ _ _ _ => n + 8192 end.
Definition ek_b (ek : enq_kind) (lst : Z) : Z := match ek with EkAppend _ _ _ _ _ _ _ _ => lst | EkNew _ _ _ _ _ _ _ _ _ _ b _ => b end.
Definition dk_glst (g : gqd) (lst : Z) : Z := if g_drain g then g_lst g else lst.

(* [comment removed for export] *)
Definition ek_pre (ek : enq_kind) (RNG : footprint) (t nb lst n hm : Z) (m : amem) : Prop :=
  match ek with
  | EkAppend nx bsz cnt hs cnt24 maxc csz stj =>
         0 < nb /\ rw_cells asegs m lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 cnt)]
      /\ 0 <= cnt < 1021 /\ 0 <= bsz /\ bsz + n < 2^63 /\ 0 <= nx < 2^64
      /\ u64arr asegs m (lst + 24) hs /\ length hs = Z.to_nat cnt
      /\ (exists bs, rw_cells asegs m (lst + 24 + 8 * cnt) [CB (Z.to_nat (8192 - 24 - 8 * cnt)) bs])
      /\ 0x10007fff8000 <= lst /\ lst + 8192 <= ATOP /\ (t + 4096 <= lst \/ lst + 8192 <= t) /\ (hm + 16 <= lst \/ lst + 8192 <= hm)
      /\ rw_cells asegs m (t + 2128) [C4 (Z_to_bv 64 cnt24); C4 maxc; C8 csz] /\ rw_cells asegs m (t + 2784) [C8 stj]   (* [comment removed for export] *)
      /\ rng RNG lst 8192
  | EkNew full nx bsz cnt24 maxc csz stj idxw chunks spacebeg b hs =>
         (if full then 0 < nb /\ rw_cells asegs m lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)]
                    /\ 0 <= nx < 2^64 /\ 0 <= bsz < 2^64 /\ 0x10007fff8000 <= lst /\ lst + 8192 <= ATOP
                    /\ u64arr asegs m (lst + 24) hs /\ length hs = 1021%nat    (* [comment removed for export] *)
                    /\ rng RNG lst 8192
          else nb = 0 /\ lst = 0)
      /\ rw_cells asegs m 0xab3b8 [C8 (Z_to_bv 64 spacebeg)]
      /\ rw_cells asegs m (t + 2128) [C4 (Z_to_bv 64 cnt24); C4 maxc; C8 csz]
      /\ u32arr asegs m (t + 2128 + 16) chunks /\ length chunks = 16%nat
      /\ 0 < cnt24 <= 16 /\ nth_error chunks (Z.to_nat (cnt24 - 1)) = Some idxw /\ bv_unsigned idxw < 2^32
      /\ rw_cells asegs m (t + 2784) [C8 stj]
      /\ b = spacebeg + 24 * 2^32 + 16 * bv_unsigned idxw
      /\ (exists bs, rw_cells asegs m b [CB (Z.to_nat 8192) bs])
      /\ 0 < spacebeg /\ 0x10007fff8000 <= b /\ b + 8192 <= ATOP
      /\ (t + 4096 <= b \/ b + 8192 <= t) /\ (t + 4096 <= lst \/ lst + 8192 <= t \/ lst = 0) /\ (b + 8192 <= lst \/ lst + 8192 <= b)
      /\ (hm + 16 <= b \/ b + 8192 <= hm) /\ (hm + 16 <= lst \/ lst + 8192 <= hm)
      /\ rng RNG b 8192
  end.

(* [comment removed for export] *)
Definition ek_post (ek : enq_kind) (t lst hm n : Z) (m' : amem) : Prop :=
  match ek with
  | EkAppend nx bsz cnt hs cnt24 maxc csz stj =>
         rw_cells asegs m' lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 (bsz + n)); C8 (Z_to_bv 64 (cnt + 1))]
      /\ u64arr asegs m' (lst + 24) (hs ++ [Z_to_bv 64 hm])
      /\ (exists bs, rw_cells asegs m' (lst + 24 + 8 * (cnt + 1)) [CB (Z.to_nat (8192 - 24 - 8 * (cnt + 1))) bs])
      /\ rw_cells asegs m' (t + 2128) [C4 (Z_to_bv 64 cnt24); C4 maxc; C8 csz] /\ rw_cells asegs m' (t + 2784) [C8 stj]
  | EkNew full nx bsz cnt24 maxc csz stj idxw chunks spacebeg b hs =>
         rw_cells asegs m' (t + 2128) [C4 (Z_to_bv 64 (cnt24 - 1)); C4 maxc; C8 csz]
      /\ (exists stj' : word, rw_cells asegs m' (t + 2784) [C8 stj'])
      /\ rw_cells asegs m' b [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (n + 8192)); C8 (Z_to_bv 64 1)]
      /\ u64arr asegs m' (b + 24) [Z_to_bv 64 hm]
      /\ (exists bs, rw_cells asegs m' (b + 24 + 8 * 1) [CB (Z.to_nat (8192 - 24 - 8 * 1)) bs])
      /\ (if full then rw_cells asegs m' lst [C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)] /\ u64arr asegs m' (lst + 24) hs else True)
  end.

(* [comment removed for export] *)
Definition dk_pre (ek : enq_kind) (g : gqd) (RNG : footprint) (t lst hm qb' : Z) (m : amem) : Prop :=
     rw_cells asegs m 0xab708 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
  /\ rw_cells asegs m 0xab710 [C8 (Z_to_bv 64 (g_nb g)); C8 (Z_to_bv 64 (g_fst g)); C8 (Z_to_bv 64 (g_lst g)); C8 (Z_to_bv 64 (g_qb g))]
  /\ 0 <= g_nb g < 2^62 /\ 0 <= g_qb g /\ 0 <= g_fst g < 2^64 /\ 0 <= g_lst g < 2^64
  /\ if g_drain g then
          Q_CACHE < qb' /\ g_qb g + qb' <= Q_MAX
       /\ (if g_full g then 0 < g_nb g /\ rw_cells asegs m (g_lst g) [C8 (Z_to_bv 64 (g_nx g))] /\ 0x10007fff8000 <= g_lst g /\ g_lst g + 8192 <= ATOP
                          /\ (t + 4096 <= g_lst g \/ g_lst g + 8192 <= t) /\ (hm + 16 <= g_lst g \/ g_lst g + 8 <= hm)
                          /\ (lst + 8192 <= g_lst g \/ g_lst g + 8192 <= lst) /\ (ek_b ek lst + 8192 <= g_lst g \/ g_lst g + 8192 <= ek_b ek lst)
                          /\ rng RNG (g_lst g) 8192
           else g_nb g = 0 /\ g_lst g = 0)
     else qb' <= Q_CACHE.

Definition dk_post (g : gqd) (nb' fst' lst' qb' : Z) (m' : amem) : Prop :=
     rw_cells asegs m' 0xab708 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
  /\ if g_drain g then
          rw_cells asegs m' 0xab710 [C8 (Z_to_bv 64 (g_nb g + nb')); C8 (Z_to_bv 64 (if g_full g then g_fst g else fst'));
                                C8 (Z_to_bv 64 lst'); C8 (Z_to_bv 64 (g_qb g + qb'))]
       /\ (if g_full g then rw_cells asegs m' (g_lst g) [C8 (Z_to_bv 64 fst')] else True)
     else rw_cells asegs m' 0xab710 [C8 (Z_to_bv 64 (g_nb g)); C8 (Z_to_bv 64 (g_fst g)); C8 (Z_to_bv 64 (g_lst g)); C8 (Z_to_bv 64 (g_qb g))].
(* [comment removed for export] *)
Definition tcache_post (g : gqd) (nb' fst' lst' qb' : Z) : list cell :=
  if g_drain g then [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
  else [C8 (Z_to_bv 64 nb'); C8 (Z_to_bv 64 fst'); C8 (Z_to_bv 64 lst'); C8 (Z_to_bv 64 qb')].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition put_tail_post (ek : enq_kind) (g : gqd)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t hm n nb fst0 lst qb b1 actx lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 144, bv_unsigned sp); (shad (hm + 16), shad (hm + 16) + shlen (rup n 8));
              (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792);
              (lst, lst + qsz lst); (ek_b ek lst, ek_b ek lst + 8192);      (* [comment removed for export] *)
              (0xab708, 0xab708 + 4); (0xab710, 0xab710 + 32); (dk_glst g lst, dk_glst g lst + 8)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) (repeat (Z_to_bv 8 253) (Z.to_nat (shlen (rup n 8))))]
    /\ rw_cells asegs m' hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)]
    /\ rw_cells asegs m' (t + 80) (tcache_post g (ek_nb ek nb) (ek_fst ek fst0) (ek_lst ek lst) (qb + ek_delta ek n))
    /\ ek_post ek t lst hm n m'
    /\ dk_post g (ek_nb ek nb) (ek_fst ek fst0) (ek_lst ek lst) (qb + ek_delta ek n) m'.

Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

Definition put_tail_spec__stmt : Prop := forall (ek : enq_kind) (g : gqd) (t hm lst : Z) RNG
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n nb fst0 qb b1 actx lo : Z) (sjunk : list byte),
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
  0 <= nb < 2^62 -> 0 <= qb -> qb + n + 8192 < 2^62 -> 0 <= fst0 < 2^64 -> 0 <= lst < 2^64 ->
  sclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> t mod 4096 = 0 -> (hm + 16 <= t \/ t + 4096 <= hm) ->
  ek_pre ek RNG t nb lst n hm m ->
  dk_pre ek g RNG t lst hm (qb + ek_delta ek n) m ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 -> rng RNG hm 16 -> rng RNG (shad (hm + 16)) (shlen (rup n 8)) ->
  iclr t 4096 ->                                            (* [comment removed for export] *)
  evtF asegs RNG (put_tail_post ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n nb fst0 lst qb b1 actx lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3805c) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable ek : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 0).
Variable g : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 1).
Variable t : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 2).
Variable hm : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 3).
Variable lst : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 4).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 5).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 6).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 7).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 8).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 9).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 10).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 11).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 12).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 13).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 14).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 15).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 16).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 17).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 18).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 19).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 20).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 21).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 22).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 23).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 24).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 25).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 26).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 27).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 28).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 29).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 30).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 31).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 32).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 33).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 34).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 35).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 36).
Variable F : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 37).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 38).
Variable m : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 39).
Variable n : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 40).
Variable nb : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 41).
Variable fst0 : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 42).
Variable qb : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 43).
Variable b1 : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 44).
Variable actx : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 45).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 46).
Variable sjunk : ltac2:(SecDietF.SzSecF.ty 'put_tail_spec__stmt 47).
#[using="Type"] Lemma put_tail_spec__body : ltac:(let T := type of (fun (h : put_tail_spec__stmt) => h ek g t hm lst RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n nb fst0 qb b1 actx lo sjunk) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (ek, (g, (t, (hm, (lst, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (n, (nb, (fst0, (qb, (b1, (actx, (lo, sjunk)))))))))))))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO MI -> -> -> -> -> QK GF FLG PC HD N B1 AL HLO TCH HHI HCE SH QC NB QB QBN FST LST T0 T1 TAL DHT EK DK RIMG RTLS RSTK RT RH RSH TI.
  band_int TI. (pose proof (ablk_lin _ _ HLO) as ndP__; nd_pre ndP__ 4%nat; intros HL1 HL2 HL3 HL4; nd_post). unfold AIMG_HI in HL1. band_int HLO. band_lin. band_int T0.   (* [comment removed for export] *)
  assert (SHB : 2148239360 <= shad (hm + 16) /\ shad (hm + 16) + shlen (rup n 8) <= 0x10007fff8000).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold Q_MAX in N. Z.div_mod_to_equations. lia. }
  assert (RUP : n <= rup n 8 <= n + 7 /\ rup n 8 mod 8 = 0) by (unfold rup; Z.div_mod_to_equations; lia).
  assert (SHL : 0 < shlen (rup n 8) < 0x10000000) by (unfold shlen; rewrite Z.shiftr_div_pow2 by lia; unfold Q_MAX in N; Z.div_mod_to_equations; lia).
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (shad (hm + 16), shad (hm + 16) + shlen (rup n 8));
              (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792);
              (lst, lst + qsz lst); (ek_b ek lst, ek_b ek lst + 8192);      (* [comment removed for export] *)
              (0xab708, 0xab708 + 4); (0xab710, 0xab710 + 32); (dk_glst g lst, dk_glst g lst + 8)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  (nd_pre PC 7%nat; intros P1 P2 P3 P4 P5 P6 P7; nd_post).
  pose proof QK as QK0. rw_split QK0 1%nat QMX QK2. clear QK2.
  box DHT.
  (* [comment removed for export] *)
  destruct ek as [nx bsz cnt hs cnt24' maxc' csz' stj' | full nx bsz cnt24 maxc csz stj idxw chunks spacebeg b hs0];
  [ (nd_pre EK 16%nat; intros NB1 LB CNT BSZ BSZN NX LA LEN [junkt LJ] L0 L1 DTL DHL CR' STS' RL; nd_post); box DTL; box DHL
  | (nd_pre EK 20%nat; intros FULL SB CR CH LCH CNT NTH IXS STS HB [junkb BJ] SBP B0 BL1 DTB DTL DBL DHB DHL RB; nd_post);
    box DTB; box DTL; box DBL; box DHB; box DHL;
    destruct full; [(nd_pre FULL 9%nat; intros NB1 LB NX BSZ L0 L1 LA0 LEN0 RL; nd_post); assert (LEN0Z : Z.of_nat (length hs0) = 1021) by (rewrite LEN0; reflexivity); box LEN0 | destruct FULL as [NB0 LST0]] ];
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
    box HD. box SH'. box GLB. box CR'. box STS'.
    snapshot [(bv_unsigned sp + -80 - 64, bv_unsigned sp + -80); (t + 80 + 24, t + 80 + 32); (lst + 8, lst + 24); (lst + 24 + 8 * cnt, lst + 24 + 8 * cnt + 8)]%Z MUe WMe.
    box LJ. box LB. box QC. box LA.   (* [comment removed for export] *)
    box ST.
    call_sp (enqueue_append_spec (t + 80) lst cnt RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz lo hs);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| reflexivity| unboxed QC| lia| lia| unfold Q_MAX in *; lia| lia| lia| lia
      | unboxed LB| exact CNT| lia| unfold Q_MAX in *; lia| lia| unboxed LA| exact LEN| exists junkt; unboxed LJ
      | iclr_of TI| atop_facts; lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia|].
    try clear ST.
    clear LJ LB QC LA.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ylia). carry SH' MUe WMe ltac:(lia). carry GLB MUe WMe ltac:(ub G5; ub G7; ylia). carry CR' MUe WMe ltac:(ub DTL; ylia). carry STS' MUe WMe ltac:(ub DTL; ylia). clear MUe WMe.
    rename POST into LJ'. rename PC1 into LB'. rename PC2 into LA'. rename PC0 into QC'. destruct LJ' as [junkt' LJ'].
    (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].   (* [comment removed for export] *)
    step. step. step. step.                    (* [comment removed for export] *)
    box HD.  box LB'. box LA'. box LJ'. box CR'. box STS'.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0xab708, 0xab708 + 4); (0xab710, 0xab710 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GLB. box GC. box MX.   (* [comment removed for export] *)
    box ST.
    step. call_sp (drain_norecycle_spec true t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 lst (qb + n) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| lia| lia
      | exact QMX| split; [lia|]; split; [unboxed GLB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try lia; ub G5; ylia| exact TI| atop_facts; lia|].
    try clear ST.
    clear QC' GLB GC MX.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT; ub G6; ylia). carry LB' MUd WMd ltac:(ub DTL; first [ub G7 | pose proof GLST0]; ylia). carry LA' MUd WMd ltac:(rewrite length_app, LEN; cbn [length]; ub DTL; first [ub G7 | pose proof GLST0]; ylia). carry LJ' MUd WMd ltac:(ub DTL; first [ub G7 | pose proof GLST0]; ylia). carry CR' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; ylia). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; ylia). clear MUd WMd.
    do 10 step.
    release_frame FRP ST (bv_unsigned sp).
    unfold put_tail_post. rewrite ?QZE. unfold tcache_post, dk_post, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).   (* [comment removed for export] *)  all: try (eexists; eassumption).
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
    box HD. box SH'. box CR'. box STS'.
    snapshot [(bv_unsigned sp + -80 - 64, bv_unsigned sp + -80); (t + 80 + 24, t + 80 + 32); (lst + 8, lst + 24); (lst + 24 + 8 * cnt, lst + 24 + 8 * cnt + 8)]%Z MUe WMe.
    box LJ. box LB. box QC. box LA.   (* [comment removed for export] *)
    box ST.
    call_sp (enqueue_append_spec (t + 80) lst cnt RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz lo hs);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| reflexivity| unboxed QC| lia| lia| unfold Q_MAX in *; lia| lia| lia| lia
      | unboxed LB| exact CNT| lia| unfold Q_MAX in *; lia| lia| unboxed LA| exact LEN| exists junkt; unboxed LJ
      | iclr_of TI| atop_facts; lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia|].
    try clear ST.
    clear LJ LB QC LA.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ylia). carry SH' MUe WMe ltac:(lia). carry CR' MUe WMe ltac:(ub DTL; ylia). carry STS' MUe WMe ltac:(ub DTL; ylia). clear MUe WMe.
    rename POST into LJ'. rename PC1 into LB'. rename PC2 into LA'. rename PC0 into QC'. destruct LJ' as [junkt' LJ'].
    (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].   (* [comment removed for export] *)
    step. step. step. step.                    (* [comment removed for export] *)
    box HD.  box LB'. box LA'. box LJ'. box CR'. box STS'.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0xab708, 0xab708 + 4); (0xab710, 0xab710 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GC. box MX.   (* [comment removed for export] *)
    box ST.
    step. call_sp (drain_norecycle_spec false t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 lst (qb + n) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| lia| lia
      | exact QMX| exact GNB0| exact TI| atop_facts; lia| exact I|].
    try clear ST.
    clear QC' GC MX.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT;  ylia). carry LB' MUd WMd ltac:(ub DTL; first [ub G7 | pose proof GLST0]; ylia). carry LA' MUd WMd ltac:(rewrite length_app, LEN; cbn [length]; ub DTL; first [ub G7 | pose proof GLST0]; ylia). carry LJ' MUd WMd ltac:(ub DTL; first [ub G7 | pose proof GLST0]; ylia). carry CR' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; ylia). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; ylia). clear MUd WMd.
    do 10 step.
    release_frame FRP ST (bv_unsigned sp).
    unfold put_tail_post. rewrite ?QZE. unfold tcache_post, dk_post, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).   (* [comment removed for export] *)  all: try (eexists; eassumption).
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
    box HD. box SH'. box CR'. box STS'.
    snapshot [(bv_unsigned sp + -80 - 64, bv_unsigned sp + -80); (t + 80 + 24, t + 80 + 32); (lst + 8, lst + 24); (lst + 24 + 8 * cnt, lst + 24 + 8 * cnt + 8)]%Z MUe WMe.
    box LJ. box LB. box QC. box LA.   (* [comment removed for export] *)
    box ST.
    call_sp (enqueue_append_spec (t + 80) lst cnt RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz lo hs);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| reflexivity| unboxed QC| lia| lia| unfold Q_MAX in *; lia| lia| lia| lia
      | unboxed LB| exact CNT| lia| unfold Q_MAX in *; lia| lia| unboxed LA| exact LEN| exists junkt; unboxed LJ
      | iclr_of TI| atop_facts; lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia|].
    try clear ST.
    clear LJ LB QC LA.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ylia). carry SH' MUe WMe ltac:(lia). carry CR' MUe WMe ltac:(ub DTL; ylia). carry STS' MUe WMe ltac:(ub DTL; ylia). clear MUe WMe.
    rename POST into LJ'. rename PC1 into LB'. rename PC2 into LA'. rename PC0 into QC'. destruct LJ' as [junkt' LJ'].
    (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. if_cases KD; zify_cond KD; [exfalso; unfold Q_CACHE in *; lia|].   (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    do 10 step.
    release_frame FRP ST (bv_unsigned sp).
    unfold put_tail_post. rewrite ?QZE. unfold tcache_post, dk_post, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).   (* [comment removed for export] *)  all: try (eexists; eassumption).
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
    box HD. box CH. box SH'. box GLB. box LA0.
    snapshot [(bv_unsigned sp + -80 - 64, bv_unsigned sp + -80); (t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box LB. box QC.   (* [comment removed for export] *)
    box ST.
    call_sp (enqueue_new_spec true t lst b RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt24 spacebeg lo maxc csz stj idxw chunks);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| reflexivity| reflexivity| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | split; [lia|]; split; [unboxed LB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try assumption; lia
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia|].
    try clear ST.
    clear BJ STS CR LB QC.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; ylia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; ylia). carry SH' MUe WMe ltac:(lia). carry LA0 MUe WMe ltac:(rewrite LEN0Z; ub DTL; ub DBL; ylia). carry GLB MUe WMe ltac:(ub G5; ub G7; ub G8; ylia). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].
    (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].   (* [comment removed for export] *)
    step. step. step. step.                    (* [comment removed for export] *)
    box HD.  box PC3. box PC4. box PC5. box POST. box PC1. box STS'. box LA0.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0xab708, 0xab708 + 4); (0xab710, 0xab710 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GLB. box GC. box MX. box CH.   (* [comment removed for export] *)
    box ST.
    step. call_sp (drain_norecycle_spec true t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (nb + 1) fst0 b (qb + (n + 8192)) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| lia| lia
      | exact QMX| split; [lia|]; split; [unboxed GLB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try lia; ub G5; ylia| exact TI| atop_facts; lia|].
    try clear ST.
    clear QC' GLB GC MX CH.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT; ub G6; ylia). carry PC3 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; ylia). carry PC4 MUd WMd ltac:(cbn [length]; ub DTB; first [ub G8 | pose proof GLST0]; ylia). carry PC5 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; ylia). carry POST MUd WMd ltac:(ub DTL; first [ub G7 | pose proof GLST0]; ylia). carry PC1 MUd WMd ltac:(first [ub G5 | pose proof GLST0]; ylia). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; ylia). carry LA0 MUd WMd ltac:(rewrite LEN0Z; ub DTL; first [ub G7 | pose proof GLST0]; ylia). clear MUd WMd.
    do 10 step.
    release_frame FRP ST (bv_unsigned sp).
    unfold put_tail_post. rewrite ?QZE. unfold tcache_post, dk_post, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).   (* [comment removed for export] *)  all: try (eexists; eassumption).
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
    box HD. box CH. box SH'. box LA0.
    snapshot [(bv_unsigned sp + -80 - 64, bv_unsigned sp + -80); (t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box LB. box QC.   (* [comment removed for export] *)
    box ST.
    call_sp (enqueue_new_spec true t lst b RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt24 spacebeg lo maxc csz stj idxw chunks);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| reflexivity| reflexivity| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | split; [lia|]; split; [unboxed LB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try assumption; lia
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia|].
    try clear ST.
    clear BJ STS CR LB QC.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; ylia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; ylia). carry SH' MUe WMe ltac:(lia). carry LA0 MUe WMe ltac:(rewrite LEN0Z; ub DTL; ub DBL; ylia). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].
    (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].   (* [comment removed for export] *)
    step. step. step. step.                    (* [comment removed for export] *)
    box HD.  box PC3. box PC4. box PC5. box POST. box PC1. box STS'. box LA0.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0xab708, 0xab708 + 4); (0xab710, 0xab710 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GC. box MX.   (* [comment removed for export] *)
    box ST.
    step. call_sp (drain_norecycle_spec false t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (nb + 1) fst0 b (qb + (n + 8192)) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| lia| lia
      | exact QMX| exact GNB0| exact TI| atop_facts; lia| exact I|].
    try clear ST.
    clear QC' GC MX.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT;  ylia). carry PC3 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; ylia). carry PC4 MUd WMd ltac:(cbn [length]; ub DTB; first [ub G8 | pose proof GLST0]; ylia). carry PC5 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; ylia). carry POST MUd WMd ltac:(ub DTL; first [ub G7 | pose proof GLST0]; ylia). carry PC1 MUd WMd ltac:(first [ub G5 | pose proof GLST0]; ylia). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; ylia). carry LA0 MUd WMd ltac:(rewrite LEN0Z; ub DTL; first [ub G7 | pose proof GLST0]; ylia). clear MUd WMd.
    do 10 step.
    release_frame FRP ST (bv_unsigned sp).
    unfold put_tail_post. rewrite ?QZE. unfold tcache_post, dk_post, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).   (* [comment removed for export] *)  all: try (eexists; eassumption).
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
    box HD. box CH. box SH'. box LA0.
    snapshot [(bv_unsigned sp + -80 - 64, bv_unsigned sp + -80); (t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box LB. box QC.   (* [comment removed for export] *)
    box ST.
    call_sp (enqueue_new_spec true t lst b RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt24 spacebeg lo maxc csz stj idxw chunks);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| reflexivity| reflexivity| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | split; [lia|]; split; [unboxed LB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try assumption; lia
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia|].
    try clear ST.
    clear BJ STS CR LB QC.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; ylia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; ylia). carry SH' MUe WMe ltac:(lia). carry LA0 MUe WMe ltac:(rewrite LEN0Z; ub DTL; ub DBL; ylia). clear MUe WMe.
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
    box HD. box CH. box SH'. box GLB.
    snapshot [(bv_unsigned sp + -80 - 64, bv_unsigned sp + -80); (t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box QC.   (* [comment removed for export] *)
    box ST.
    call_sp (enqueue_new_spec false t lst b RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt24 spacebeg lo maxc csz stj idxw chunks);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| reflexivity| reflexivity| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | exact NB0
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia| exact I|].
    try clear ST.
    clear BJ STS CR QC.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; ylia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; ylia). carry SH' MUe WMe ltac:(lia). carry GLB MUe WMe ltac:(ub G5; ub G7; ub G8; ylia). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].
    (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].   (* [comment removed for export] *)
    step. step. step. step.                    (* [comment removed for export] *)
    box HD.  box PC3. box PC4. box PC5. box PC1. box STS'.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0xab708, 0xab708 + 4); (0xab710, 0xab710 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GLB. box GC. box MX. box CH.   (* [comment removed for export] *)
    box ST.
    step. call_sp (drain_norecycle_spec true t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (nb + 1) b b (qb + (n + 8192)) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| lia| lia
      | exact QMX| split; [lia|]; split; [unboxed GLB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try lia; ub G5; ylia| exact TI| atop_facts; lia|].
    try clear ST.
    clear QC' GLB GC MX CH.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT; ub G6; ylia). carry PC3 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; ylia). carry PC4 MUd WMd ltac:(cbn [length]; ub DTB; first [ub G8 | pose proof GLST0]; ylia). carry PC5 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; ylia). carry PC1 MUd WMd ltac:(first [ub G5 | pose proof GLST0]; ylia). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; ylia). clear MUd WMd.
    do 10 step.
    release_frame FRP ST (bv_unsigned sp).
    unfold put_tail_post. rewrite ?QZE. unfold tcache_post, dk_post, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).   (* [comment removed for export] *)  all: try (eexists; eassumption).
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
    box HD. box CH. box SH'.
    snapshot [(bv_unsigned sp + -80 - 64, bv_unsigned sp + -80); (t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box QC.   (* [comment removed for export] *)
    box ST.
    call_sp (enqueue_new_spec false t lst b RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt24 spacebeg lo maxc csz stj idxw chunks);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| reflexivity| reflexivity| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | exact NB0
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia| exact I|].
    try clear ST.
    clear BJ STS CR QC.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; ylia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; ylia). carry SH' MUe WMe ltac:(lia). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].
    (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].   (* [comment removed for export] *)
    step. step. step. step.                    (* [comment removed for export] *)
    box HD.  box PC3. box PC4. box PC5. box PC1. box STS'.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0xab708, 0xab708 + 4); (0xab710, 0xab710 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GC. box MX.   (* [comment removed for export] *)
    box ST.
    step. call_sp (drain_norecycle_spec false t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (nb + 1) b b (qb + (n + 8192)) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| lia| lia
      | exact QMX| exact GNB0| exact TI| atop_facts; lia| exact I|].
    try clear ST.
    clear QC' GC MX.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT;  ylia). carry PC3 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; ylia). carry PC4 MUd WMd ltac:(cbn [length]; ub DTB; first [ub G8 | pose proof GLST0]; ylia). carry PC5 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; ylia). carry PC1 MUd WMd ltac:(first [ub G5 | pose proof GLST0]; ylia). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; ylia). clear MUd WMd.
    do 10 step.
    release_frame FRP ST (bv_unsigned sp).
    unfold put_tail_post. rewrite ?QZE. unfold tcache_post, dk_post, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).   (* [comment removed for export] *)  all: try (eexists; eassumption).
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
    box HD. box CH. box SH'.
    snapshot [(bv_unsigned sp + -80 - 64, bv_unsigned sp + -80); (t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box QC.   (* [comment removed for export] *)
    box ST.
    call_sp (enqueue_new_spec false t lst b RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt24 spacebeg lo maxc csz stj idxw chunks);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| reflexivity| reflexivity| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | exact NB0
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia| exact I|].
    try clear ST.
    clear BJ STS CR QC.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; ylia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; ylia). carry SH' MUe WMe ltac:(lia). clear MUe WMe.
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
End Zd1.
#[using="Type"] Lemma put_tail_spec : ltac:(let t := eval cbv delta [put_tail_spec__stmt] in put_tail_spec__stmt in exact t).
Proof. exact put_tail_spec__body. Qed.
End CANSEC1.
End TwB.
