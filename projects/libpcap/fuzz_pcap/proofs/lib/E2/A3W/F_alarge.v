(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import MM_syscalls.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecFacts. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecSlog__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_memchr__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3 F_acache3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_s__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_acalloc_iseg__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.ASecSlog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.RT_stubs OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memchr__A3W.F_memset OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison0 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acache3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_ammap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_iseg__A3W.F_ammapz.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From Ltac2 Require Import Ltac2.
Local Ltac2 rec zt_skel (cs : constant FSet.t) (t : constr) : bool :=
  if zt_plain_arith_s cs t then true else
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      if lt_is_ref h reference:(or) then (if zt_skel cs (Array.get args 0) then zt_skel cs (Array.get args 1) else false)
      else if lt_is_ref h reference:(and) then (if zt_skel cs (Array.get args 0) then zt_skel cs (Array.get args 1) else false)
      else if lt_is_ref h reference:(not) then zt_skel cs (Array.get args 0)
      else if lt_is_ref h reference:(iff) then (if zt_skel cs (Array.get args 0) then zt_skel cs (Array.get args 1) else false)
      else false
  | Constr.Unsafe.Prod b c =>
      if Constr.Unsafe.noccurn 1 c then (if zt_skel cs (Constr.Binder.type b) then zt_skel cs c else false) else false
  | _ => false
  end.
Local Ltac2 zt_prune_keepor () : unit :=
  let hs := Control.hyps () in
  let cs := zt_plain_consts () in
  let extra := List.exist (fun h => let (id, body, ty) := h in
                 match body with
                 | Some _ => false
                 | None => if zt_is_local id then (if zt_plain_arith_s cs ty then false else zt_skel cs ty) else false
                 end) hs in
  if extra then
    let ids := List.map_filter (fun h => let (id, body, ty) := h in
                  match body with
                  | Some _ => None
                  | None => if zt_skel cs ty then None else if zt_is_local id then zt_is_prop_some ty id else None
                  end) hs in
    match ids with [] => () | _ :: _ => Std.clear ids end
  else Control.zero (Tactic_failure None).
Local Ltac zify_prune_keepor := ltac2:(Control.enter zt_prune_keepor).
Set Default Proof Mode "Classic".
Local Ltac Stdlib.micromega.Lia.lia ::=
  first [ zify_prune; first [ zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                            | Zify.zify; xlia zchecker ]
        | zify_prune_keepor; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
Local Ltac zrange_gz_g :=
  lazymatch goal with
  | |- inr64 (Z.sub (cb_sm _) (Z.land (Z.shiftr (cb_sm _) (1)%Z) (6148914691236517205)%Z)) => fail   (* [comment removed for export] *)
  | |- inr64 (Z.add (Z.b2z (Z.ltb _ _)) (-1)%Z) => fail   (* [comment removed for export] *)
  | |- inr64 (Z.sub (0)%Z (Z.b2z (Z.ltb _ _))) => fail   (* [comment removed for export] *)
  (* [comment removed for export] *)
  | |- inr64 (Z.add (Z.land _ (3689348814741910323)%Z) (Z.land (Z.shiftr _ (2)%Z) (3689348814741910323)%Z)) => fail   (* [comment removed for export] *)
  | |- inr64 (Z.add (Z.add (Z.land _ (3689348814741910323)%Z) (Z.land (Z.shiftr _ (2)%Z) (3689348814741910323)%Z)) (Z.shiftr _ (4)%Z)) => fail   (* [comment removed for export] *)
  | |- inr64 (Z.mul (Z.land _ (1085102592571150095)%Z) (72340172838076673)%Z) => fail   (* [comment removed for export] *)
  | |- _ => zrange
  end.
Local Ltac zrange_gz_i :=
  lazymatch goal with
  | |- inr64 (Z.add (bv_unsigned _) _) => fail   (* [comment removed for export] *)
  | |- _ => zrange
  end.
Local Ltac zsimp ::=
  rewrite ?v_sltu_b2z, ?v_slt_b2z, ?v_sltiu_b2z, ?v_slti_b2z;
  cbv delta [zxb];
  zb_fold_lits;
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?e)] =>
      first [ rewrite (inr64_unsigned_lit e) by zrange_gz_g
            | zs_wrap e ]            (* [comment removed for export] *)
  | |- _ => progress zs_idioms
  end; zb_fold_lits.
Local Ltac zsimp_in H ::=
  rewrite ?v_sltu_b2z, ?v_slt_b2z, ?v_sltiu_b2z, ?v_slti_b2z in H;
  cbv delta [zxb] in H;
  zb_fold_lits_in H;
  repeat match type of H with
  | context [bv_unsigned (Z_to_bv 64 ?e)] =>
      first [ rewrite (inr64_unsigned_lit e) in H by zrange_gz_i
            | zs_wrap_in e H ]
  | _ => progress (zs_idioms_in H)
  end; zb_fold_lits_in H.
Local Ltac d_is_natlit n ::= sl_is_natlit n.
Local Ltac is_natlit n ::= sl_is_natlit n.
Local Ltac flia ::= first [ sassumption | clear; lia | slim; lia | lia | assumption ].   (* [comment removed for export] *)
Import ListNotations.
Import Exc.
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
Local Ltac fp_cheap8 := first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs end | clear ]; Stdlib.micromega.Lia.lia.   (* [comment removed for export] *)
Local Ltac fp_find8c := first [ apply Exists_cons_hd; cbn [fst snd]; split; fp_cheap8 | apply Exists_cons_tl; fp_find8c ].
Local Ltac fp_find8 := first [ apply Exists_cons_hd; cbn [fst snd]; split; lia | apply Exists_cons_tl; fp_find8 ].
Local Ltac fp_cover8 := apply sub_fp_cover8; repeat (apply Forall_cons; [ cbn [fst snd]; first [left; fp_cheap8 | right; fp_find8c | right; fp_find8] | ]); apply Forall_nil.
(* [comment removed for export] *)
Local Ltac transport_call_munch_tac ::= first [ fp_cover8 | unfold sub_fp; cbn [outside]; first [ match goal with Hs : bv_unsigned _ = bv_unsigned _ + _ |- _ => clear -Hs; intros; lia end | clear; intros; lia | intros; slia ] ].
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac dlia := repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

Local Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.
(* [comment removed for export] *)
Local Ltac easm := first [ lazymatch goal with |- rw_cells ?s ?mm ?A _ => match goal with H : rw_cells s mm A _ |- _ => exact H end end | eassumption ].
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
Definition large_entry := 0x38660.
End CANSEC1.
Notation LARGE_STACK := 464 (only parsing).   (* [comment removed for export] *)

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT} {tlsI : ABase.atlsT}.
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
Definition large_cells (ctx t PA : Z) (m : amem) : Prop :=
     rmap_cells m /\ poison_cells m
  /\ rw_cells asegs m 0xa5498 [C8 (Z_to_bv 64 0xa7398)] /\ rw_cells asegs m 0xa7398 [C8 (Z_to_bv 64 0x19361)]
  /\ rw_cells asegs m 0xade60 [C1 (Z_to_bv 8 1)] /\ rw_cells asegs m 0xade64 [C4 (Z_to_bv 64 0)]
  /\ rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] /\ rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)]
  /\ rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)]
  /\ rw_cells asegs m 0xaafd8 [C8 (Z_to_bv 64 4096); C8 (Z_to_bv 64 PA); C8 (Z_to_bv 64 PA)].      (* [comment removed for export] *)

#[using="Type"] Lemma large_cells_frame : forall ctx t PA m m' W, large_cells ctx t PA m -> munch W m m' -> wmono asegs m m' ->
  AIMG_HI <= ctx ->
  Forall (fun iv => (((snd iv <= AIMG_LO \/ AIMG_HI <= fst iv) /\ (snd iv <= ATPv + -88 \/ ATPv + -80 <= fst iv)) /\ (snd iv <= ctx + 152 \/ ctx + 160 <= fst iv))      (* [comment removed for export] *)
                    \/ (0xaaff0 <= fst iv /\ snd iv <= 0xad800)) W -> large_cells ctx t PA m'.
Proof.
  intros ctx t PA m m' W LC MU WM CX HW.
  (nd_pre LC 10%nat; intros (Q1 & Q2 & Q3 & Q4 & Q5) (P1 & P2 & P3 & P4 & P5 & P6 & P7) R3 R4 R5 R6 R7 R8 R9 R10; nd_post).
  unfold AIMG_HI, AIMG_LO, ATP88, ATSD in *.
  assert (D : forall A k, 0 <= k -> ((0x10000 <= A /\ A + k <= 0xaaff0) \/ (0xad800 <= A /\ A + k <= 0x603000) \/ (A = ctx + 152 /\ k = 8) \/ (A = ATPv + -88 /\ k = 8)) -> disjoint_from W A k).      (* [comment removed for export] *)
  { pose proof atp_lin as TLN. clear -HW CX TLN. intros A k Hk HA. induction W as [|[lo hi] W IH]; cbn; [exact I|]. inversion HW; subst. cbn in *. split; [lia| apply IH; assumption]. }      (* [comment removed for export] *)
  unfold large_cells, rmap_cells, poison_cells. repeat lazymatch goal with |- _ /\ _ => split end;
    (eapply rw_cells_transport; [eassumption | exact MU | exact WM | unfold ATP88, ATSD; cbn; apply D; lia]).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma zeros32_hdr : forall m A, fill_at m A 32 0 ->
  rw_cells asegs m A [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
Proof. intros m A H. eapply rw_cells_recast; [exact H | cbn; tauto | vm_compute; reflexivity | reflexivity]. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma mtx_to_C4 : forall m (b : Z), 0 <= b < 256 ->
  rw_cells asegs m 0xab240 [C1 (Z_to_bv 8 b); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m 0xab240 [C4 (Z_to_bv 64 b)].
Proof.
  intros m b Hb H. eapply rw_cells_recast; [exact H | cbn; tauto | | reflexivity].
  cbn [cells_bytes cbytes app]. replace b with (b + 256 * 0) at 1 by lia. rewrite (le4_two_bytes b 0) by lia. reflexivity.
Qed.
#[using="Type"] Lemma mtx_of_C4 : forall m (b : Z), 0 <= b < 256 ->
  rw_cells asegs m 0xab240 [C4 (Z_to_bv 64 b)] ->
  rw_cells asegs m 0xab240 [C1 (Z_to_bv 8 b); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Proof.
  intros m b Hb H. eapply rw_cells_recast; [exact H | cbn; tauto | | reflexivity].
  cbn [cells_bytes cbytes app]. replace b with (b + 256 * 0) at 2 by lia. rewrite (le4_two_bytes b 0) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Definition large_post (RNG : footprint) (sp : word) (a n ctx t PA nres nsec nres' lo : Z) (m : amem)
    (RNG' : footprint) (m' : amem) : Prop :=
  let size := needed_size n in let ms := sec_map_size n in let res := a + 4096 in let ue := res + size in
     fp_le RNG RNG' /\ fp_bw RNG'
  /\ a mod 4096 = 0 /\ ablk a (a + ms) /\ a + ms <= ATOP            (* [comment removed for export] *)
  /\ munch [(bv_unsigned sp - LARGE_STACK, bv_unsigned sp); (a, a + ms); (shad a, shad a + ms / 8);
            (AINSTANCE + 112, AINSTANCE + 720); (t + 2800, t + 3168);
            (PA + 8 * nsec, PA + 8 * nsec + 8); (PA + 8 * nres, PA + 8 * nres')]%Z m m'
  /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
     (* [comment removed for export] *)
  /\ rw_cells asegs m' a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 size); C8 (Z_to_bv 64 nsec);
                          CB (Z.to_nat (4096 - 32)) (repeat (Z_to_bv 8 0) (Z.to_nat (4096 - 32)))]
  /\ rw_cells asegs m' res [CB (Z.to_nat (ms - 4096)) (repeat (Z_to_bv 8 0) (Z.to_nat (ms - 4096)))]
  /\ fill_at m' (shad a) 512 0xfa
  /\ fill_at m' (shad a + 512) (size / 8) 0
  /\ fill_at m' (shad a + 512 + size / 8) (ms / 8 - 512 - size / 8) 0xfa
  /\ rng RNG' a ms /\ rng RNG' (shad a) (ms / 8)
     (* [comment removed for export] *)
  /\ rw_cells asegs m' 0xab008 [C8 (Z_to_bv 64 nres'); C8 (Z_to_bv 64 (nsec + 1))]
  /\ rw_cells asegs m' 0xab018 [C1 (Z_to_bv 8 0)]
  /\ junk_at m' 0xab020 32 /\ junk_at m' 0xab040 512
  /\ rw_cells asegs m' 0xab240 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
  /\ junk_at m' 0xab258 16
  /\ (exists sj', u64arr asegs m' (t + 2800) sj' /\ length sj' = 46%nat)
  /\ rw_cells asegs m' (PA + 8 * nsec) [C8 (Z_to_bv 64 a)]
  /\ ((nsec <> nres /\ nres' = nres)
      \/ (nsec = nres /\ nres' = nres + 16384
          /\ rw_cells asegs m' (PA + 8 * nres + 8) [CB (Z.to_nat (131072 - 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (131072 - 8)))]
          /\ rng RNG' (PA + 8 * nres) 131072))
  /\ nres' <= 1048576
  /\ large_cells ctx t PA m'.

(* [comment removed for export] *)
#[using="Type"] Lemma c8x4_of_junk : forall m A, junk_at m A 32 -> exists w1 w2 w3 w4 : word, rw_cells asegs m A [C8 w1; C8 w2; C8 w3; C8 w4].
Proof.
  intros m A J. destruct (junk_split m A 16 16 J ltac:(lia) ltac:(lia)) as [J1 J2].
  (nd_pre (c8c8_of_junk m A J1) 3%nat; intros w1 w2 H1; nd_post). (nd_pre (c8c8_of_junk m (A + 16) J2) 3%nat; intros w3 w4 H2; nd_post).
  exists w1, w2, w3, w4. apply (proj2 (rw_cells_app asegs m A [C8 w1; C8 w2] [C8 w3; C8 w4])). split; [exact H1| exact H2].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma lxor63 : forall k, 0 <= k <= 63 -> Z.lxor k 63 = 63 - k.
Proof.
  apply (range_by_compute (fun k => Z.lxor k 63 = 63 - k) (fun k => Z.lxor k 63 =? 63 - k) 0 63); [| vm_compute; reflexivity].
  intros z Hz. apply Z.eqb_eq. exact Hz.
Qed.

(* [comment removed for export] *)
Definition large_tail_post (sp0 : Z) (vra v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 s10v s11v gp tp a0 : word) (F : bvmap 5 word) (fc : bv 32)
    (a ms size PA nres' nsec lo : Z) (fj : list byte) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR vra (Z_to_bv 64 sp0) gp tp t0 t1 t2 v0 v1 a0 a1 a2 a3 a4 a5 a6 a7 v2 v3 v4 v5 v6 v7 v8 v9 s10v s11v t3 t4 t5 t6)
             F (ret_pc vra) fc None m' (seg_rom asegs)
    /\ munch [(sp0 - 96, sp0); (a + 24, a + 32); (0xab008, 0xab268); (PA + 8 * nsec, PA + 8 * nsec + 8)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo sp0
    /\ rw_cells asegs m' a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 size); C8 (Z_to_bv 64 nsec)]
    /\ rw_cells asegs m' 0xab008 [C8 (Z_to_bv 64 nres'); C8 (Z_to_bv 64 (nsec + 1))]
    /\ rw_cells asegs m' 0xab018 [C1 (Z_to_bv 8 0)]
    /\ junk_at m' 0xab020 32 /\ junk_at m' 0xab040 512
    /\ rw_cells asegs m' 0xab240 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ junk_at m' 0xab258 16
    /\ rw_cells asegs m' (PA + 8 * nsec) [C8 (Z_to_bv 64 a)].

Definition large_tail_spec__stmt : Prop := forall RNG (sp0 : Z) (vra v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 s10v s11v : word)
    ra gp tp t0 t1 t2 a0 a1 a2 a4 a5 a6 a7 s4 s6 s7 s8 s9 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (a ms size PA nres' nsec k lo : Z) (srt : byte) (fj jstats jbsl jglob jslot : list byte),
  stk asegs m lo (sp0 - 96) -> ATOP <= lo -> lo <= sp0 - 96 -> sp0 < 2^64 ->
  mem_inv asegs m ->
  rw_cells asegs m (sp0 + -96) [CB 8 fj; C8 v9; C8 v8; C8 v7; C8 v6; C8 v5; C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 vra] ->
  rw_cells asegs m 0xaafd8 [C8 (Z_to_bv 64 4096); C8 (Z_to_bv 64 PA); C8 (Z_to_bv 64 PA)] ->
  rw_cells asegs m a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 size); C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m 0xab008 [C8 (Z_to_bv 64 nres'); C8 (Z_to_bv 64 nsec)] ->
  rw_cells asegs m 0xab018 [C1 srt] ->
  rw_cells asegs m 0xab020 [CB 32 jstats] -> rw_cells asegs m 0xab040 [CB 512 jbsl] ->
  rw_cells asegs m 0xab240 [C4 (Z_to_bv 64 1)] ->
  rw_cells asegs m 0xab258 [CB 16 jglob] ->
  rw_cells asegs m (PA + 8 * nsec) [CB 8 jslot] ->
  ablk a (a + ms) -> a + ms <= ATOP -> (a + ms <= PA \/ PA + 8388608 <= a) ->
  ablk PA (PA + 8388608) -> PA + 8388608 <= ATOP -> 0 <= nsec -> 8 * nsec + 8 <= 8388608 -> 0 <= nres' < 2^64 ->
  73728 <= ms <= 536821760 -> 34 <= k <= 47 ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (sp0 - lo) -> rng RNG a ms -> rng RNG (PA + 8 * nsec) 8 ->
  evtF asegs RNG (large_tail_post sp0 vra v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 s10v s11v gp tp a0 F fc a ms size PA nres' nsec lo fj m)
    (MS (mkR ra (Z_to_bv 64 (sp0 + -96)) gp tp t0 t1 t2 (Z_to_bv 64 0xab248) (Z_to_bv 64 0xaafd8) a0 a1 a2 (Z_to_bv 64 nsec) a4 a5 a6 a7
             (Z_to_bv 64 ms) (Z_to_bv 64 k) s4 (Z_to_bv 64 a) s6 s7 s8 s9 s10v s11v t3 t4 t5 t6)
        F (Z_to_bv 64 0x388c4) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 0).
Variable sp0 : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 1).
Variable vra : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 2).
Variable v0 : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 3).
Variable v1 : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 4).
Variable v2 : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 5).
Variable v3 : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 6).
Variable v4 : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 7).
Variable v5 : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 8).
Variable v6 : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 9).
Variable v7 : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 10).
Variable v8 : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 11).
Variable v9 : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 12).
Variable s10v : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 13).
Variable s11v : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 14).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 15).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 16).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 17).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 18).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 19).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 20).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 21).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 22).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 23).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 24).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 25).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 26).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 27).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 28).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 29).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 30).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 31).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 32).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 33).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 34).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 35).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 36).
Variable F : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 37).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 38).
Variable m : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 39).
Variable a : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 40).
Variable ms : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 41).
Variable size : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 42).
Variable PA : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 43).
Variable nres' : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 44).
Variable nsec : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 45).
Variable k : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 46).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 47).
Variable srt : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 48).
Variable fj : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 49).
Variable jstats : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 50).
Variable jbsl : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 51).
Variable jglob : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 52).
Variable jslot : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 53).
#[using="Type"] Lemma large_tail_spec__body : ltac:(let T := type of (fun (h : large_tail_spec__stmt) => h RNG sp0 vra v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 s10v s11v ra gp tp t0 t1 t2 a0 a1 a2 a4 a5 a6 a7 s4 s6 s7 s8 s9 t3 t4 t5 t6 F fc m a ms size PA nres' nsec k lo srt fj jstats jbsl jglob jslot) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (sp0, (vra, (v0, (v1, (v2, (v3, (v4, (v5, (v6, (v7, (v8, (v9, (s10v, (s11v, (ra, (gp, (tp, (t0, (t1, (t2, (a0, (a1, (a2, (a4, (a5, (a6, (a7, (s4, (s6, (s7, (s8, (s9, (t3, (t4, (t5, (t6, (F, (fc, (m, (a, (ms, (size, (PA, (nres', (nsec, (k, (lo, (srt, (fj, (jstats, (jbsl, (jglob, jslot)))))))))))))))))))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO SP64 MI FR I64 ZH INS SRT JST JBS MTX JGL JSL AHI ACE DAP PA0 PA1 NS0 NS1 NR MSB KB RIMG RTLS RSTK RCH RPS.
  pose proof AHI as AHI0. pose proof PA0 as PA00. clear AHI PA0. (nd_pre (ablk_int _ _ AHI0) 6%nat; intros kA AHI AHIa AHIb AHIc AHId; nd_post). (nd_pre (ablk_int _ _ PA00) 6%nat; intros kP PA0 PA0a PA0b PA0c PA0d; nd_post).   (* [comment removed for export] *)
  atop_facts.
  pose proof (munch_refl [(sp0 - 96, sp0); (a + 24, a + 32); (0xab008, 0xab268); (PA + 8 * nsec, PA + 8 * nsec + 8)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  box DAP.
  destruct (c8_of_junk m (PA + 8 * nsec) (ex_intro _ jslot JSL)) as [wj PAS]. clear JSL.
  step.                                                        (* [comment removed for export] *)
  zstep. rewrite (lxor63 k) by (clear -KB; lia).               (* [comment removed for export] *)
  box PAS. snapshot [(a + 24, a + 32)]%Z MUh WMh.
  step.                                                        (* [comment removed for export] *)
  carry PAS MUh WMh ltac:(ub DAP; clear -Y NS0 NS1 AHI AHIa AHIb AHIc AHId MSB; dlia). clear MUh WMh.
  zstep. zstep.                                                (* [comment removed for export] *)
  setreg 12 (Z_to_bv 64 (PA + 8 * nsec)) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by (clear; lia); clear -NS0 NS1; lia).
  box ZH. snapshot [(PA + 8 * nsec, PA + 8 * nsec + 8)]%Z MUp WMp.
  remember (PA + 8 * nsec) as PS eqn:HPS.
  step.                                                        (* [comment removed for export] *)
  subst PS.
  carry ZH MUp WMp ltac:(ub DAP; clear -Y NS0 NS1 AHI AHIa AHIb AHIc AHId MSB; dlia). clear MUp WMp.
  (* [comment removed for export] *)
  (nd_pre (c8x4_of_junk _ 0xab020 (ex_intro _ jstats JST)) 5%nat; intros w1 w2 w3 w4 AST; nd_post). clear JST.
  step. step.                                                  (* [comment removed for export] *)
  zstep.                                                       (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  zstep. zstep.                                                (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  (* [comment removed for export] *)
  destruct (junk_split _ 0xab040 (8 * (63 - k)) (512 - 8 * (63 - k)) ltac:(replace (8 * (63 - k) + (512 - 8 * (63 - k))) with 512 by (clear; lia); exists jbsl; exact JBS)
              ltac:(clear -KB; lia) ltac:(clear -KB; lia)) as [JB1 JB2].
  destruct (junk_split _ (0xab040 + 8 * (63 - k)) 8 (512 - 8 * (63 - k) - 8) ltac:(replace (8 + (512 - 8 * (63 - k) - 8)) with (512 - 8 * (63 - k)) by (clear; lia); exact JB2)
              ltac:(clear; lia) ltac:(clear -KB; lia)) as [JBW JB3]. clear JB2 JBS.
  destruct (c8_of_junk _ _ JBW) as [wb BSL]. clear JBW. destruct JB1 as [bs1 JB1]. destruct JB3 as [bs3 JB3].
  remember (0xaafd8 + 8 * (63 - k)) as BSB eqn:HBSB.
  replace (0xab040 + 8 * (63 - k)) with (BSB + 104) in BSL by (subst BSB; clear; lia).
  replace (0xab040 + 8 * (63 - k) + 8) with (BSB + 112) in JB3 by (subst BSB; clear; lia).
  step. if_cases KM; zify_cond KM.
  all: try lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x38908) _ _ _ _) => step end.   (* [comment removed for export] *)
  all: zstep; zstep.                                           (* [comment removed for export] *)
  all: setreg 11 (Z_to_bv 64 BSB) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by (clear; lia); subst BSB; clear -KB; lia).
  all: step.                                                   (* [comment removed for export] *)
  all: zstep.                                                  (* [comment removed for export] *)
  all: step; step.                                             (* [comment removed for export] *)
  (* [comment removed for export] *)
  all: (nd_pre (c8c8_of_junk _ 0xab258 (ex_intro _ jglob JGL)) 3%nat; intros g0 g1 GL; nd_post); clear JGL.
  all: zstep.                                                  (* [comment removed for export] *)
  all: assert (AMO1 : amo_aligned AD (Z_to_bv 64 0xab258) = true) by (apply amo_alignedD_intro; [clear; lia| reflexivity]).
  all: amo_stepA AMO1.                                         (* [comment removed for export] *)
  all: zstep.                                                  (* [comment removed for export] *)
  all: assert (AMO2 : amo_aligned AD (Z_to_bv 64 0xab260) = true) by (apply amo_alignedD_intro; [clear; lia| reflexivity]).
  all: amo_stepA AMO2.                                         (* [comment removed for export] *)
  all: step.                                                   (* [comment removed for export] *)
  (* [comment removed for export] *)
  all: apply (mtx_of_C4 _ 1 ltac:(clear; lia)) in MTX.
  all: step.                                                   (* [comment removed for export] *)
  (* [comment removed for export] *)
  all: do 13 step.                                             (* [comment removed for export] *)
  all: lazymatch goal with FRM : rw_cells asegs ?mm (?spz + -96) (CB 8 _ :: _) |- _ => lazymatch goal with STK : stk asegs mm ?loz _ |- _ => release_frame FRM STK spz end end.
  all: apply evtF_done; unfold large_tail_post; do 15 eexists; split; [reflexivity|].
  all: split; [assumption|]. all: split; [assumption|]. all: split; [assumption|]. all: split; [assumption|].
  all: split; [exact ZH|]. all: split; [assumption|]. all: split; [assumption|].
  all: split; [exact (junk_of_cells _ _ _ AST)|].
  all: split.
  1,3: subst BSB; replace 512 with (8 * (63 - k) + (512 - 8 * (63 - k))) by (clear; lia);
       apply junk_merge; [exists bs1; exact JB1 | | clear -KB; lia| clear -KB; lia];
       replace (512 - 8 * (63 - k)) with (8 + (512 - 8 * (63 - k) - 8)) by (clear; lia);
       apply junk_merge; [ | | clear; lia | clear -KB; lia];
       [ replace (700480 + 8 * (63 - k)) with (700376 + 8 * (63 - k) + 104) by (clear; lia); exact (junk_of_cells _ _ _ BSL)
       | replace (700480 + 8 * (63 - k) + 8) with (700376 + 8 * (63 - k) + 112) by (clear; lia); exists bs3; exact JB3 ].
  all: split; [assumption|]. all: split; [| assumption].
  all: exact (junk_of_cells _ _ _ GL).
  Unshelve. all: try (apply ref_ro_addr_false; right; lia).
Qed.
End Zd1.
#[using="Type"] Lemma large_tail_spec : ltac:(let t := eval cbv delta [large_tail_spec__stmt] in large_tail_spec__stmt in exact t).
Proof. exact large_tail_spec__body. Qed.

Definition large_spec__stmt : Prop := forall RNG {R} (K : Z -> itree node (exc R)) (K2 : Z -> Z -> itree node (exc R))
    (Q : R -> footprint -> machine_state -> Prop) (FRESH : Z -> bool)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n ctx t PA nres nsec lo : Z) (sj : list word) (sorted : Z) (jstats jbsl jglob jslot : list byte),
  let size := needed_size n in let ms := sec_map_size n in
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - LARGE_STACK ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 0xaafd8 -> a1 = Z_to_bv 64 0xab248 ->      (* [comment removed for export] *) a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 8 ->
  1 <= n <= AREQMAX -> is_primary n = false ->
  large_cells ctx t PA m ->
  (* [comment removed for export] *)
  sclr ctx 65536 -> ctx + 4096 <= ATOP -> sclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  (* [comment removed for export] *)
  rw_cells asegs m 0xab008 [C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 nsec)] ->
  rw_cells asegs m 0xab018 [C1 (Z_to_bv 8 sorted)] ->
  rw_cells asegs m 0xab020 [CB 32 jstats] ->
  rw_cells asegs m 0xab040 [CB 512 jbsl] ->
  rw_cells asegs m 0xab240 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m 0xab258 [CB 16 jglob] ->
  (* [comment removed for export] *)
  ablk PA (PA + 8388608) -> PA + 8388608 <= ATOP -> PA mod 4096 = 0 ->      (* [comment removed for export] *)
  0 <= nsec <= nres -> nres mod 16384 = 0 -> nres <= 1048576 ->
  (nsec < nres -> rw_cells asegs m (PA + 8 * nsec) [CB 8 jslot]) ->
  (PA + 8388608 <= t \/ t + 4096 <= PA) -> (PA + 8388608 <= ctx \/ ctx + 4096 <= PA) ->
  tclr PA 8388608 ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG PA (8 * nres) ->
  AIMG_HI <= ctx -> iclr t 4096 ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  (forall a, FRESH a = true ->
        ablk a (a + ms)
     /\ (a + ms <= t \/ t + 4096 <= a) /\ (a + ms <= ctx \/ ctx + 4096 <= a) /\ (a + ms <= PA \/ PA + 8388608 <= a)
     /\ fill_at m (shad a) (ms / 8) 0
     /\ tclr a ms) ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  (forall a RNG' ms', FRESH a = false -> 0 < a -> a mod 4096 = 0 -> a + ms <= ATOP -> fp_le RNG RNG' ->
      implS asegs RNG' (K a) (epostF Q) ms') ->
  (* [comment removed for export] *)
  (forall a RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      FRESH a = true -> nsec <> nres -> large_post RNG sp a n ctx t PA nres nsec nres lo m RNG' m' ->
      implS asegs RNG' (K a) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (a + 4096)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  (* [comment removed for export] *)
  (forall a, FRESH a = true -> nsec = nres -> nres + 16384 <= 1048576 ->
      K a = ebind (enode (NMmap (PA + 8 * nres) 131072 3 50) (adec_mmap ATOP 131072 3)) (K2 a)) ->
  (* [comment removed for export] *)
  (forall a RNG' ms', FRESH a = true -> nsec = nres -> 1048576 < nres + 16384 -> implS asegs RNG' (K a) (epostF Q) ms') ->
  (forall a r RNG' ms', r <> PA + 8 * nres -> 0 < r -> r + 131072 <= ATOP -> implS asegs RNG' (K2 a r) (epostF Q) ms') ->
  (forall a RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      FRESH a = true -> nsec = nres -> large_post RNG sp a n ctx t PA nres nsec (nres + 16384) lo m RNG' m' ->
      implS asegs RNG' (K2 a (PA + 8 * nres)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (a + 4096)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (ebind (enode (NMmap 0 ms 3 34) (adec_mmap ATOP ms 3)) K) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 large_entry) fc None m (seg_rom asegs)).
Section Zd2.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 0).
Variable R : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 1).
Variable K : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 2).
Variable K2 : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 3).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 4).
Variable FRESH : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 5).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 6).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 7).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 8).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 9).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 10).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 11).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 12).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 13).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 14).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 15).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 16).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 17).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 18).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 19).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 20).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 21).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 22).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 23).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 24).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 25).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 26).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 27).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 28).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 29).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 30).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 31).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 32).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 33).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 34).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 35).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 36).
Variable F : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 37).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 38).
Variable m : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 39).
Variable n : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 40).
Variable ctx : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 41).
Variable t : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 42).
Variable PA : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 43).
Variable nres : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 44).
Variable nsec : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 45).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 46).
Variable sj : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 47).
Variable sorted : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 48).
Variable jstats : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 49).
Variable jbsl : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 50).
Variable jglob : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 51).
Variable jslot : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 52).
Let size := needed_size n.
Let ms := sec_map_size n.
#[using="size ms"] Lemma large_spec__body : ltac:(let T := type of (fun (h : large_spec__stmt) => h RNG R K K2 Q FRESH ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n ctx t PA nres nsec lo sj sorted jstats jbsl jglob jslot) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (R, (K, (K2, (Q, (FRESH, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (n, (ctx, (t, (PA, (nres, (nsec, (lo, (sj, (sorted, (jstats, (jbsl, (jglob, jslot))))))))))))))))))))))))))))))))))))))))))))))))))))) as _.
 cbv zeta.
  intros ST CEIL LO MI TP -> -> -> -> N PRIM LC CX0 CX1 T0 T1 CT2 STATS LSJ INS SRT JST JBS MTX JGL
         PA0 PA1 PAL NSR NRM NRB0 JSL DPT DPC DPL RIMG RTLS RSTK RCTX RT RPA CXI TIC FROK UNR KONT1 SHAPE2 UNR3 UNR2 KONT2. band_lin.   (* [comment removed for export] *)
  pose proof PA0 as PA00. clear PA0. (nd_pre (ablk_int _ _ PA00) 6%nat; intros kP PA0 PA0a PA0b PA0c PA0d; nd_post).   (* [comment removed for export] *)
  (pose proof (sec_facts n N PRIM) as ndP__; nd_pre ndP__ 10%nat; intros NB RZ RSE RSR RSM NSE MSE MSR MSM MSB; nd_post).
  unfold AIMG_HI, AREQMAX, large_entry in *.
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - LARGE_STACK, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  chg (needed_size n) size. chg (sec_map_size n) ms.
  (* [comment removed for export] *)
  box STATS. box INS. box SRT. box JST. box JBS. box MTX. box JGL.
  (* [comment removed for export] *)
  assert (MS4 : exists q, ms = 4096 * q) by (exists (ms / 4096); clear -MSM MSB; Z.div_mod_to_equations; lia).
  clear RSE. box MSE. box RSM. box MSM. box NRM. box PAL. box CT2. box DPT. box DPC.
  (* [comment removed for export] *)
  iprefix.
  carve_frame 96%nat ST.
  do 12 step.                                                  (* [comment removed for export] *)
  assert (HWL : Forall (fun iv => (((snd iv <= AIMG_LO \/ AIMG_HI <= fst iv) /\ (snd iv <= ATPv + -88 \/ ATPv + -80 <= fst iv)) /\ (snd iv <= ctx + 152 \/ ctx + 160 <= fst iv)) \/ (0xaaff0 <= fst iv /\ snd iv <= 0xad800))
                       [(bv_unsigned sp - LARGE_STACK, bv_unsigned sp)]%Z)
    by (apply Forall_cons; [cbn; left; unfold AIMG_HI, AIMG_LO; clear -SPR CEIL LO CX1 CXI; lia | apply Forall_nil]).
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (large_cells_frame ctx t PA m mm _ LC MU WM ltac:(exact CXI) HWL) as LC1 end.
  (nd_pre LC1 10%nat; intros RC PC GNM NAME TI TK T88 TSD CT I64; nd_post). unfold ATP88, ATSD in *.
  step. zstep. zstep. step. if_lit.                            (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  zstep. zstep. step. if_lit.                                  (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.                                  (* [comment removed for export] *)
  setreg 11 (Z_to_bv 64 (ms - 4096)) ltac:(rewrite land_align4096 by (clear -MSB MSR; lia); f_equal; unbox MSE; rewrite MSE; clear -MSB; Z.div_mod_to_equations; lia).
  zstep. zstep. zstep. zstep. zstep.                           (* [comment removed for export] *)
  change (Z.land ((0 - Z.b2z (4096 <? 8)) mod 18446744073709551616) 8) with 0.
  setreg 18 (Z_to_bv 64 ms) ltac:(f_equal; clear; lia).
  step. if_cases K0; zify_cond K0. 2: { exfalso. clear -K0 MSR MSB NSE RSR N. subst size. lia. }   (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  (* [comment removed for export] *)
  apply evtF_done.
  lazymatch goal with |- implS _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
  eapply (mmapz_spec RNG K Q FRESH _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mm ms lo) end.
  all: try lazymatch goal with
       | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -SPR CEIL LO; lia); exact ST
       | |- mem_inv _ _ => assumption
       | |- rmap_cells _ => exact RC
       | |- rng_aimg _ => exact RIMG
       | |- rng_atls _ => exact RTLS
       | |- @eq word _ _ => reflexivity
       | |- _ mod 4096 = 0 => unboxed MSM
       | |- bv_unsigned _ <> 0 => rewrite unsigned_lit by (clear; lia); clear; lia
       | |- rng _ _ (_ - _) => rewrite unsigned_lit by (clear -SPR CEIL LO; lia); eapply rng_sub'; [exact RSTK|]; clear -SPR CEIL LO; lia
       end.
  all: try (atop_facts; rewrite ?unsigned_lit by (clear -SPR CEIL LO; lia); clear -SPR CEIL LO MSB; lia).
  { (* [comment removed for export] *)
    intros a HFR A0 ACE. destruct (FROK a HFR) as (AH & _). unfold ablk, KLS, AIMG_HI in *.  (* [comment removed for export] *) rewrite unsigned_lit by (clear -SPR CEIL LO; lia). clear -AH ACE CEIL LO SPR. lia. }
  { (* [comment removed for export] *)
    intros a RNG' ms' HFR A0 AAL ACE LE. eapply UNR; eassumption. }
  (* [comment removed for export] *)
  intros a RNG' m2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HFR PO.
  (nd_pre PO 13%nat; intros FPLE BW AAL A0 ACE MU2 WM2 MI2 ST2 ZCH RCH RSCH RC2; nd_post).
  (nd_pre (FROK a HFR) 6%nat; intros AHI DAT DAC DAP SH0 DAL; nd_post). box DAT. box DAC. box DAP.
  pose proof AHI as AHI0. clear AHI. (nd_pre (ablk_int _ _ AHI0) 6%nat; intros kA AHI AHIa AHIb AHIc AHId; nd_post).   (* [comment removed for export] *)
  rewrite unsigned_lit in MU2, ST2 by (clear -SPR CEIL LO; lia).
  (* [comment removed for export] *)
  destruct (Z_lt_le_dec nsec 1048576) as [NSB|NSB].
  2: { eapply UNR3; [exact HFR | clear -NSB NSR NRB0; lia | clear -NSB NSR NRB0; lia]. }
  (* [comment removed for export] *)
  set (CW := if nsec =? nres then 131072 else 0).
  assert (ECW : CW = (if nsec =? nres then 131072 else 0)) by reflexivity.
  assert (CWF : 0 <= CW <= 131072 /\ 8 * nres + CW <= 8388608).
  { rewrite ECW. ub NRM. destruct (Z.eqb_spec nsec nres) as [E|E]; clear -NSB NSR NRB0 Y E; Z.div_mod_to_equations; lia. }
  clearbody CW. box ECW.
  atop_facts.
  assert (SZ8 : size mod 8 = 0) by (rewrite NSE; ub RSM; clear -Y; Z.div_mod_to_equations; lia).
  assert (SZP : 0 < size) by (rewrite NSE; clear -RSR N; lia).
  assert (SHR : 0x800b8600 <= shad a /\ shad a + ms / 8 <= 0x10007fff8000 /\ shlen ms = ms / 8 /\ shlen 4096 = 512
                /\ shad (a + 4096 + size) = shad a + 512 + size / 8 /\ shlen (ms - 4096 - size) = ms / 8 - 512 - size / 8).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by (clear; lia). change (2^3) with 8. ub MSM. clear -AHI AHIa AHIb AHIc AHId ACE MSB AAL SZ8 K0 Y. Z.div_mod_to_equations. lia. }
  (nd_pre SHR 6%nat; intros SH1 SH2 SH3 SH4 SH5 SH6; nd_post). rewrite SH3 in RSCH.
  (nd_pre (ablk_shad_int _ _ AHI0 ltac:(clear -AAL; Z.div_mod_to_equations; lia) ltac:(clear -MSB; lia)) 6%nat; intros kS ASD ASDa ASDb _ _; nd_post).   (* [comment removed for export] *)
  (nd_pre (sclr_int _ _ T0 ltac:(clear -TIC; lia) ltac:(clear -T1; lia)) 4%nat; intros kT TBND TBNDa TBNDb; nd_post). (nd_pre (sclr_int _ _ CX0 ltac:(clear -CXI; lia) ltac:(clear -CX1; lia)) 4%nat; intros kC CBND CBNDa CBNDb; nd_post).   (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (MU02 : munch [(bv_unsigned sp - LARGE_STACK, bv_unsigned sp + -96); (a, a + ms)]%Z m0 m2)
    by (eapply munch_weaken; [| exact MU2]; unfold sub_fp; cbn [outside]; clear; intros q Hq; lia).
  assert (MUA : munch [(bv_unsigned sp - LARGE_STACK, bv_unsigned sp); (a, a + ms)]%Z m m2).
  { eapply munch_trans; [eapply munch_weaken; [| exact MU] | eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside]; clear; intros q Hq; lia. }
  assert (WMA : wmono asegs m m2) by (eapply wmono_trans; [exact WM | exact WM2]).
  clear MU WM MU2.
  xport FR MU02 WM2 ltac:(clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE; dlia).
  xport I64 MU02 WM2 ltac:(clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE; dlia).
  xport GNM MU02 WM2 ltac:(clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE; dlia). xport NAME MU02 WM2 ltac:(clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE; dlia).
  xport TI MU02 WM2 ltac:(clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE; dlia). xport TK MU02 WM2 ltac:(clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE; dlia).
  xport T88 MU02 WM2 ltac:((nd_pre (tclr_int_lem _ _ DAL ltac:(clear -AHIa; lia) ltac:(clear -AHId; atop_facts; lia)) 4%nat; intros kL DALk DALa DALb; nd_post); clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE DALk DALa DALb; dlia).      (* [comment removed for export] *) xport TSD MU02 WM2 ltac:(clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE; dlia).
  xport CT MU02 WM2 ltac:(ub DAC; clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE CX0 CX1 Y CXI; dlia).
  assert (PC2 : poison_cells m2).
  { eapply poison_cells_frame; [exact PC | exact MU02 | exact WM2 |]. unfold AIMG_HI.
    apply Forall_cons; [cbn; clear -SPR CEIL LO; lia|]. apply Forall_cons; [cbn; clear -AHI AHIa AHIb AHIc AHId; lia| apply Forall_nil]. }
  clear PC RC ST.
  unfold fill_at in SH0. xport SH0 MUA WMA ltac:(clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE SH1 SH2 MSB; dlia).
  unbox STATS. xport STATS MUA WMA ltac:(ub DAT; rewrite LSJ; clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE T0 T1 Y TIC; dlia).
  unbox INS. xport INS MUA WMA ltac:(clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE; dlia).
  unbox SRT. xport SRT MUA WMA ltac:(clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE; dlia).
  unbox JST. xport JST MUA WMA ltac:(clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE; dlia).
  unbox JBS. xport JBS MUA WMA ltac:(clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE; dlia).
  unbox MTX. xport MTX MUA WMA ltac:(clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE; dlia).
  unbox JGL. xport JGL MUA WMA ltac:(clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE; dlia).
  assert (JSL2 : nsec < nres -> rw_cells asegs m2 (PA + 8 * nsec) [CB 8 jslot]).
  { intros LT. specialize (JSL LT). xport JSL MUA WMA ltac:(ub DAP; clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF LT Y; dlia). exact JSL. }
  clear JSL.
  (* [comment removed for export] *)
  change (rw_cells asegs m2 (shad a) [CB (Z.to_nat (ms / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (ms / 8)))]) with (fill_at m2 (shad a) (ms / 8) 0) in SH0.
  destruct (fill_split m2 (shad a) 512 (ms / 8 - 512) 0 ltac:(replace (512 + (ms / 8 - 512)) with (ms / 8) by (clear; lia); exact SH0) ltac:(clear; lia) ltac:(clear -MSB; Z.div_mod_to_equations; lia))
    as [SHH SHR0].
  destruct (fill_split m2 (shad a + 512) (size / 8) (ms / 8 - 512 - size / 8) 0 ltac:(replace (size / 8 + (ms / 8 - 512 - size / 8)) with (ms / 8 - 512) by (clear; lia); exact SHR0)
              ltac:(clear -SZP; Z.div_mod_to_equations; lia) ltac:(ub MSM; clear -MSB K0 SZ8 Y MSR; Z.div_mod_to_equations; lia))
    as [SHU SHT]. clear SHR0.
  clear SH0.
  (* [comment removed for export] *)
  apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RTLS. apply (rng_fp_le _ _ _ _ FPLE) in RSTK. apply (rng_fp_le _ _ _ _ FPLE) in RCTX.
  apply (rng_fp_le _ _ _ _ FPLE) in RT. apply (rng_fp_le _ _ _ _ FPLE) in RPA.
  iprefix.
  replace (ret_pc (Z_to_bv 64 231196)) with (Z_to_bv 64 231196 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
  step. if_cases K1; zify_cond K1. { exfalso. clear -K1 A0 ACE. lia. }          (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  zstep. zstep.                                                (* [comment removed for export] *)
  setreg 11 (Z_to_bv 64 0) ltac:(f_equal; rewrite (Z.land_comm 4095 a); change 4095 with (Z.ones 12); rewrite Z.land_ones by (clear -A0; lia); change (2^12) with 4096; symmetry; exact AAL).
  step. if_lit.                                                (* [comment removed for export] *)
  zstep. zstep. zstep.                                         (* [comment removed for export] *)
  setreg 11 (Z_to_bv 64 0) ltac:(f_equal; change 7 with (Z.ones 3); rewrite Z.land_ones by (clear -A0; lia); change (2^3) with 8; clear -AAL A0; Z.div_mod_to_equations; lia).
  zstep. zstep. zstep. zstep. zstep.                           (* [comment removed for export] *)
  change ((Z.b2z (0 <? 1) + -1) mod 18446744073709551616) with 0. change (Z.land 0 8) with 0.
  setreg 25 (Z_to_bv 64 (a + 4096)) ltac:(f_equal; clear; lia).
  zstep. zstep. zstep. zstep.                                  (* [comment removed for export] *)
  setreg 23 (Z_to_bv 64 (a + 4096 + size))
    ltac:(f_equal; change 18446744073709551608 with (2^64 - 2^3); rewrite land_align_down by (clear -A0 ACE K0 SZP; lia);
          change (2^3) with 8; clear -AAL SZ8 A0; Z.div_mod_to_equations; lia).
  setreg 10 (Z_to_bv 64 (a + 4096))
    ltac:(f_equal; change 18446744073709551608 with (2^64 - 2^3); rewrite land_align_down by (clear -A0 ACE K0 MSB; lia);
          change (2^3) with 8; clear -AAL A0; Z.div_mod_to_equations; lia).
  zstep. step. step.                                           (* [comment removed for export] *)
  setreg 11 (Z_to_bv 64 4096) ltac:(f_equal; clear; lia).
  (* [comment removed for export] *)
  clear MU02.
  apply (munch_weaken _ [(bv_unsigned sp - LARGE_STACK, bv_unsigned sp); (a, a + ms); (shad a, shad a + ms / 8);
                          (0xab008, 0xab268); (t + 2800, t + 3168);
                          (PA + 8 * nsec, PA + 8 * nsec + 8); (PA + 8 * nres, PA + 8 * nres + CW)]%Z) in MUA.
  2: { unfold sub_fp. cbn [outside]. clear. intros q Hq. tauto. }
  (* [comment removed for export] *)
  unfold fill_at in SHH, SHU, SHT.
  pose proof PC2 as PCx. (nd_pre PCx 7%nat; intros P1 P2 P3 P4 P5 P6 P7; nd_post).
  pose proof RC2 as RCx. (nd_pre RCx 5%nat; intros Q1 Q2 Q3 Q4 Q5; nd_post). clear PC2 RC2 Q3.
  Local Ltac pcells := unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end); assumption.
  (* [comment removed for export] *)
  assert (RSH1 : rng RNG' (shad a) 512) by (eapply rng_sub'; [exact RSCH|]; clear -MSB; Z.div_mod_to_equations; lia).
  pose proof (munch_refl [(bv_unsigned sp + -96 - 64, bv_unsigned sp + -96); (shad a, shad a + 512)]%Z m2) as MUS. pose proof (wmono_refl asegs m2) as WMS.
  match goal with H : stk asegs ?mm _ _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into STK__; box STK__ end. box SHH.   (* [comment removed for export] *)
  step. call_sp (poison_shadow_spec_k RNG' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a 4096 512 250 lo).   (* [comment removed for export] *)
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => try clear STK__; try clear SHH
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- stk _ _ _ _ => unboxed STK__
       | |- mem_inv _ _ => assumption
       | |- poison_cells _ => pcells
       | |- @eq word _ _ => reflexivity
       | |- rw_cells _ _ (shad _) _ => unboxed SHH
       | |- rng _ (shad _) _ => exact RSH1
       | |- rng_aimg _ => exact RIMG
       | |- rng_atls _ => exact RTLS
       | |- shlen _ = _ => exact SH4
       | |- rng _ _ _ => solve_rng
       end.
  all: try (eapply ablk_sub; [exact AHI0 | clear; lia | clear -MSB; lia]).
  all: try (atop_facts; clear -AAL A0 AHI AHIa AHIb AHIc AHId ACE MSB SPR CEIL LO; first [lia | Z.div_mod_to_equations; lia]).
  lazymatch goal with M : munch _ m2 ?mm, W : wmono asegs m2 _ |- _ =>
    assert (JSL3 : nsec < nres -> rw_cells asegs mm (PA + 8 * nsec) [CB 8 jslot])
      by (intros LT; specialize (JSL2 LT); xport JSL2 M W ltac:(clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF LT SH1 SH2 MSB; dlia); exact JSL2);
    clear JSL2 M W; rename JSL3 into JSL2 end.
  (* [comment removed for export] *)
  zstep. step. step.                                           (* [comment removed for export] *)
  setreg 11 (Z_to_bv 64 (ms - 4096 - size)) ltac:(f_equal; clear; lia).
  assert (RSH2 : rng RNG' (shad (a + 4096 + size)) (ms / 8 - 512 - size / 8))
    by (rewrite SH5; eapply rng_sub'; [exact RSCH|]; ub MSM; clear -MSB MSR SZP SZ8 K0 Y; Z.div_mod_to_equations; lia).
  rewrite <- SH5 in SHT.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (munch_refl [(bv_unsigned sp + -96 - 64, bv_unsigned sp + -96); (shad (a + 4096 + size), shad (a + 4096 + size) + (ms / 8 - 512 - size / 8))]%Z mm) as MUS;
    pose proof (wmono_refl asegs mm) as WMS end.
  match goal with H : stk asegs ?mm _ _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into STK__; box STK__ end. box SHT.   (* [comment removed for export] *)
  step. call_sp (poison_shadow_spec0_k RNG' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (a + 4096 + size) (ms - 4096 - size) (ms / 8 - 512 - size / 8) 250 lo).   (* [comment removed for export] *)
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => try clear STK__; try clear SHT
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- stk _ _ _ _ => unboxed STK__
       | |- mem_inv _ _ => assumption
       | |- poison_cells _ => pcells
       | |- @eq word _ _ => reflexivity
       | |- rw_cells _ _ (shad _) _ => unboxed SHT
       | |- rng _ (shad _) _ => exact RSH2
       | |- rng_aimg _ => exact RIMG
       | |- rng_atls _ => exact RTLS
       | |- shlen _ = _ => exact SH6
       | |- rng _ _ _ => solve_rng
       end.
  all: try (eapply ablk_sub; [exact AHI0 | clear -SZP; lia | clear; lia]).   (* [comment removed for export] *)
  all: try (atop_facts; ub MSM; clear -AAL A0 AHI AHIa AHIb AHIc AHId ACE MSB MSR SPR CEIL LO SZ8 SZP K0 Y; first [lia | Z.div_mod_to_equations; lia]).
  lazymatch goal with M : munch _ ?mo ?mm, W : wmono asegs ?mo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (JSL3 : nsec < nres -> rw_cells asegs mm (PA + 8 * nsec) [CB 8 jslot])
      by (intros LT; specialize (JSL2 LT); xport JSL2 M W ltac:(ub MSM; clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF LT SH1 SH2 SH5 MSB MSR SZP SZ8 K0 Y; Z.div_mod_to_equations; dlia); exact JSL2);
    clear JSL2 M W; rename JSL3 into JSL2 end.
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (munch_refl [(bv_unsigned sp + -96 - 32, bv_unsigned sp + -96)]%Z mm) as MUS; pose proof (wmono_refl asegs mm) as WMS end.
  pose proof CT as CT0. box CT0. box ZCH. box POST. box POST0. box SHU.   (* [comment removed for export] *)
  match goal with H : stk asegs ?mm _ _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into STK__; box STK__ end.   (* [comment removed for export] *)
  step. call_sp (thread_stats_spec RNG' ctx t lo).   (* [comment removed for export] *)
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => try clear STK__
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- stk _ _ _ _ => unboxed STK__
       | |- mem_inv _ _ => assumption
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- rw_cells _ _ _ _ => assumption
       | |- rng_aimg _ => exact RIMG
       | |- rng_atls _ => exact RTLS
       | |- rng _ _ _ => solve_rng
       end.
  all: try (unfold AIMG_HI; clear -CEIL LO CX0 CX1 T0 T1 SPR CXI TIC; lia).
  lazymatch goal with M : munch _ ?mo ?mm, W : wmono asegs ?mo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (JSL3 : nsec < nres -> rw_cells asegs mm (PA + 8 * nsec) [CB 8 jslot])
      by (intros LT; specialize (JSL2 LT); xport JSL2 M W ltac:(clear -SPR CEIL LO PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF LT; dlia); exact JSL2);
    clear JSL2; rename JSL3 into JSL2;
    (* [comment removed for export] *)
    apply (munch_weaken _ [(bv_unsigned sp + -96 - 32, bv_unsigned sp + -96); (t + 2872, t + 2888)]%Z) in M;
    [ rename M into MUS2; rename W into WMS2 | unfold sub_fp; cbn [outside]; clear; intros q Hq; tauto ] end.
  clear CT.
  (* [comment removed for export] *)
  snapshot [(t + 2872, t + 2888); (a, a + 32); (0xab240, 0xab244)]%Z MUz WMz.
  aload STATS 9 (t + 2800 + 72).                               (* [comment removed for export] *)
  aload STATS 10 (t + 2800 + 80).                              (* [comment removed for export] *)
  zstep.                                                       (* [comment removed for export] *)
  setreg 14 (Z_to_bv 64 0) ltac:(f_equal; change 7 with (Z.ones 3); rewrite Z.land_ones by (clear -A0; lia); change (2^3) with 8; clear -AAL A0; Z.div_mod_to_equations; lia).
  zstep. zstep.                                                (* [comment removed for export] *)
  astore STATS 9.                                              (* [comment removed for export] *)
  astore STATS 10.                                             (* [comment removed for export] *)
  carry ZCH MUS2 WMS2 ltac:(ub DAT; clear -Y SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB T1 TIC; dlia).
  carry POST MUS2 WMS2 ltac:(clear -SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB SH1 SH2 SH4 T1 TBND TBNDa TBNDb; dlia).   (* [comment removed for export] *)
  carry SHU MUS2 WMS2 ltac:(clear -SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB MSR SH1 SH2 SH4 SZP K0 T1 TBND TBNDa TBNDb; Z.div_mod_to_equations; dlia).
  carry POST0 MUS2 WMS2 ltac:(rewrite SH5; ub MSM; clear -Y SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB MSR SH1 SH2 SH4 SZP SZ8 K0 T1 TBND TBNDa TBNDb; Z.div_mod_to_equations; dlia).
  clear MUS2 WMS2.
  step. if_lit.                                                (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  zstep. zstep.                                                (* [comment removed for export] *)
  setreg 12 (Z_to_bv 64 0) ltac:(f_equal; try rewrite (Z.land_comm 4095); change 4095 with (Z.ones 12); rewrite Z.land_ones by (clear -A0; lia); change (2^12) with 4096; clear -AAL A0; Z.div_mod_to_equations; lia).
  step. if_lit.                                                (* [comment removed for export] *)
  step. if_cases K5; zify_cond K5. { exfalso. clear -K5 A0 SZP ACE MSR. lia. }       (* [comment removed for export] *)
  step. if_cases K6; zify_cond K6. { exfalso. clear -K6 A0 SZP ACE MSR. lia. }       (* [comment removed for export] *)
  zstep.                                                       (* [comment removed for export] *)
  setreg 21 (Z_to_bv 64 a) ltac:(f_equal; clear; lia).
  (* [comment removed for export] *)
  lazymatch type of ZCH with rw_cells _ ?mq _ _ =>
    change (fill_at mq a ms 0) in ZCH;
    destruct (fill_split mq a 32 (ms - 32) 0 ltac:(replace (32 + (ms - 32)) with ms by (clear; lia); exact ZCH) ltac:(clear; lia) ltac:(clear -MSB; lia)) as [ZH ZR];
    destruct (fill_split mq (a + 32) (4096 - 32) (ms - 4096) 0 ltac:(replace (4096 - 32 + (ms - 4096)) with (ms - 32) by (clear; lia); exact ZR) ltac:(clear; lia) ltac:(clear -MSB; lia)) as [ZP ZU]
  end.
  clear ZCH ZR. apply zeros32_hdr in ZH. unfold fill_at in ZP, ZU. replace (a + 32 + (4096 - 32)) with (a + 4096) in ZU by (clear; lia).
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (JSL3 : nsec < nres -> rw_cells asegs mm (PA + 8 * nsec) [CB 8 jslot])
      by (intros LT; specialize (JSL2 LT); xport JSL2 MUz WMz ltac:(ub DPT; ub DAP; clear -Y Y0 SPR CEIL LO PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF LT T1 AHI AHIa AHIb AHIc AHId ACE MSB TIC; dlia); exact JSL2);
    clear JSL2 MUz WMz; rename JSL3 into JSL2 end.
  box STATS. box ZP. box ZU. box POST. box POST0. box SHU.   (* [comment removed for export] *)
  snapshot [(bv_unsigned sp - LARGE_STACK, bv_unsigned sp); (a, a + 32); (0xab008, 0xab268);
            (PA + 8 * nsec, PA + 8 * nsec + 8); (PA + 8 * nres, PA + 8 * nres + CW)]%Z MUr WMr.
  snapshot [(a, a + 32); (0xab240, 0xab244)]%Z MUq WMq.      (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  step. if_cases K7; zify_cond K7. { exfalso. clear -K7 MSB. lia. }                 (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep. step. zstep. step.                                    (* [comment removed for export] *)
  apply (mtx_to_C4 _ 0 ltac:(clear; lia)) in MTX.
  assert (AMO : amo_aligned AW (Z_to_bv 64 700992) = true) by (apply amo_alignedW_intro; [clear; lia| reflexivity]).
  amo_stepA AMO.                                               (* [comment removed for export] *)
  step. zstep. zstep. zstep.                                   (* [comment removed for export] *)
  amo_stepA AMO.                                               (* [comment removed for export] *)
  step. if_lit.                                                (* [comment removed for export] *)
  zstep. step. if_lit.                                         (* [comment removed for export] *)
  (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  zstep.                                                       (* [comment removed for export] *)
  setreg 11 (Z_to_bv 64 0) ltac:(f_equal; rewrite Z.shiftr_div_pow2 by (clear; lia); clear -NSR NSB; Z.div_mod_to_equations; lia).
  step. if_lit.                                                (* [comment removed for export] *)
  (* [comment removed for export] *)
  pose proof (slog_facts ms MSB ltac:(ub MSM; exact Y)) as [CSR CLZ].
  (* [comment removed for export] *)
  do 5 zstep.                                                  (* [comment removed for export] *)
  remember (Z.lor ms (Z.shiftr ms 1)) as y1 eqn:Ey1. assert (Ry1 : (0 <= y1 < 2^64)%Z) by (change (inr64 y1); rewrite Ey1; zrange).
  do 5 zstep.                                                  (* [comment removed for export] *)
  remember (Z.lor y1 (Z.shiftr y1 2)) as y2 eqn:Ey2. assert (Ry2 : (0 <= y2 < 2^64)%Z) by (change (inr64 y2); rewrite Ey2; zrange).
  do 8 zstep.                                                  (* [comment removed for export] *)
  remember (Z.lor y2 (Z.shiftr y2 4)) as y3 eqn:Ey3. assert (Ry3 : (0 <= y3 < 2^64)%Z) by (change (inr64 y3); rewrite Ey3; zrange).
  do 2 zstep. remember (Z.lor y3 (Z.shiftr y3 8)) as y4 eqn:Ey4. assert (Ry4 : (0 <= y4 < 2^64)%Z) by (change (inr64 y4); rewrite Ey4; zrange).
  do 2 zstep. remember (Z.lor y4 (Z.shiftr y4 16)) as y5 eqn:Ey5. assert (Ry5 : (0 <= y5 < 2^64)%Z) by (change (inr64 y5); rewrite Ey5; zrange).
  do 2 zstep. remember (Z.lor y5 (Z.shiftr y5 32)) as y6 eqn:Ey6. assert (Ry6 : (0 <= y6 < 2^64)%Z) by (change (inr64 y6); rewrite Ey6; zrange).
  zstep.                                                       (* [comment removed for export] *)
  setreg 11 (Z_to_bv 64 (cb_sm ms)) ltac:(subst y6 y5 y4 y3 y2 y1; reflexivity).              (* [comment removed for export] *)
  zstep. clear Ry6 Ey6 y6 Ry5 Ey5 y5 Ry4 Ey4 y4 Ry3 Ey3 y3 Ry2 Ey2 y2 Ry1 Ey1 y1.   (* [comment removed for export] *)
  do 6 zstep. step. do 9 zstep.                                (* [comment removed for export] *)
  setreg 19 (Z_to_bv 64 (cb_clz (cb_sm ms))) ltac:(reflexivity).
  step. if_cases KQ; zify_cond KQ.
  - (* [comment removed for export] *)
    clear MUq WMq JSL2. subst nsec.
    assert (NRB : nres + 16384 <= 1048576) by (ub NRM; clear -NSB Y NSR; Z.div_mod_to_equations; lia).
    assert (ECW1 : CW = 131072) by (ub ECW; rewrite Z.eqb_refl in Y; exact Y).
    clear CWF. assert (CWF : CW = 131072 /\ nres + 16384 <= 1048576) by (split; [exact ECW1| exact NRB]).
    step.                                                      (* [comment removed for export] *)
    zstep. zstep. zstep.                                       (* [comment removed for export] *)
    setreg 11 (Z_to_bv 64 (PA + 8 * nres)) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by (clear; lia); clear -NSR; lia).
    step. step. step. step.                                    (* [comment removed for export] *)
    step.                                                      (* [comment removed for export] *)
    apply evtF_done. rewrite (SHAPE2 a HFR eq_refl NRB).
    lazymatch goal with |- implS _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (rmapd_spec RNG' (K2 a) Q _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mm (PA + 8 * nres) 131072 lo) end.
    all: try lazymatch goal with
         | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -SPR CEIL LO; lia); eassumption
         | |- mem_inv _ _ => assumption
         | |- rmap_cells _ => unfold rmap_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end); assumption
         | |- rng_aimg _ => exact RIMG
         | |- rng_atls _ => exact RTLS
         | |- @eq word _ _ => reflexivity
         | |- rng _ _ (_ - _) => rewrite unsigned_lit by (clear -SPR CEIL LO; lia); eapply rng_sub'; [exact RSTK|]; clear -SPR CEIL LO; lia
         | |- (_ + 8 * _) mod 4096 = 0 => ub NRM; ub PAL; clear -Y Y0 NSR; Z.div_mod_to_equations; lia
         end.
    all: try (unfold AIMG_HI; rewrite ?unsigned_lit by (clear -SPR CEIL LO; lia); clear -SPR CEIL LO PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF; lia).
    { (* [comment removed for export] *) intros r RNG'' ms' NE R0 RCE. eapply UNR2; [exact NE | exact R0 | exact RCE]. }
    (* [comment removed for export] *)
    intros RNG'' mc q0 q1 q2 b1 b2 b3 b4 b5 b6 b7 q3 q4 q5 q6 PM.
    (nd_pre PM 11%nat; intros FPLE2 PCE MUc WMc MIc STc ZC RPC RSPC BW2 RCc; nd_post).
    rewrite unsigned_lit in MUc, STc by (clear -SPR CEIL LO; lia).
    (* [comment removed for export] *)
    xport FR MUc WMc ltac:(clear -SPR CEIL LO PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF AHI AHIa AHIb AHIc AHId ACE MSB SH1 SH2; dlia).
    xport I64 MUc WMc ltac:(clear -SPR CEIL LO PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF AHI AHIa AHIb AHIc AHId ACE MSB SH1 SH2; dlia).
    xport INS MUc WMc ltac:(clear -SPR CEIL LO PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF AHI AHIa AHIb AHIc AHId ACE MSB SH1 SH2; dlia).
    xport SRT MUc WMc ltac:(clear -SPR CEIL LO PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF AHI AHIa AHIb AHIc AHId ACE MSB SH1 SH2; dlia).
    xport JST MUc WMc ltac:(clear -SPR CEIL LO PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF AHI AHIa AHIb AHIc AHId ACE MSB SH1 SH2; dlia).
    xport JBS MUc WMc ltac:(clear -SPR CEIL LO PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF AHI AHIa AHIb AHIc AHId ACE MSB SH1 SH2; dlia).
    xport MTX MUc WMc ltac:(clear -SPR CEIL LO PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF AHI AHIa AHIb AHIc AHId ACE MSB SH1 SH2; dlia).
    xport JGL MUc WMc ltac:(clear -SPR CEIL LO PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF AHI AHIa AHIb AHIc AHId ACE MSB SH1 SH2; dlia).
    (* [comment removed for export] *)
    xport ZH MUc WMc ltac:(ub DAP; clear -Y SPR CEIL LO PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF AHI AHIa AHIb AHIc AHId ACE MSB; dlia).
    lazymatch type of MUr with munch ?Wr ?ma ?mb =>
      assert (MUr2 : munch Wr ma mc) by (eapply munch_trans; [exact MUr | eapply munch_weaken; [| exact MUc]; unfold sub_fp; cbn [outside]; clear -CWF; intros q Hq; lia]);
      assert (WMr2 : wmono asegs ma mc) by (eapply wmono_trans; [exact WMr | exact WMc]) end.
    clear MUr WMr. rename MUr2 into MUr. rename WMr2 into WMr.
    lazymatch type of MUA with munch ?Wa ?ma ?mb =>
      assert (MUA2 : munch Wa ma mc) by (eapply munch_trans; [exact MUA | eapply munch_weaken; [| exact MUc]; unfold sub_fp; cbn [outside]; clear -CWF; intros q Hq; lia]);
      assert (WMA2 : wmono asegs ma mc) by (eapply wmono_trans; [exact WMA | exact WMc]) end.
    clear MUA WMA MUc WMc. rename MUA2 into MUA. rename WMA2 into WMA.
    apply (rng_fp_le _ _ _ _ FPLE2) in RIMG. apply (rng_fp_le _ _ _ _ FPLE2) in RTLS. apply (rng_fp_le _ _ _ _ FPLE2) in RSTK. apply (rng_fp_le _ _ _ _ FPLE2) in RCH.
    apply (rng_fp_le _ _ _ _ FPLE2) in RSCH. apply (rng_fp_le _ _ _ _ FPLE2) in RPA.
    iprefix.
    replace (ret_pc (Z_to_bv 64 232124)) with (Z_to_bv 64 232124 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
    step.                                                      (* [comment removed for export] *)
    step. step.                                                (* [comment removed for export] *)
    step. zstep.                                               (* [comment removed for export] *)
    step.                                                      (* [comment removed for export] *)
    step.                                                      (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch type of ZC with rw_cells _ ?mq _ _ =>
      change (fill_at mq (PA + 8 * nres) 131072 0) in ZC;
      destruct (fill_split mq (PA + 8 * nres) 8 (131072 - 8) 0 ZC ltac:(clear; lia) ltac:(clear; lia)) as [ZC8 ZCR] end.
    clear ZC. unfold fill_at in ZC8, ZCR.
    assert (RPS : rng RNG'' (PA + 8 * nres) 8) by (eapply rng_sub'; [exact RPC|]; clear; lia).
    eapply evtF_cut.
    { eapply (large_tail_spec RNG'' (bv_unsigned sp)); try easm.
      all: try reflexivity.
      all: try (ub DAP; atop_facts; clear -Y CEIL LO SPR NSR NRB0 CWF PCE; lia). }
    cbv beta. intros ms9 PT. unfold large_tail_post in PT.
    (nd_pre PT 16%nat; intros u0 u1 u2 c1 c2 c3 c4 c5 c6 c7 u3 u4 u5 u6 m9 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 12%nat; intros MU9 WM9 MI9 ST9 ZH9 INS9 SRT9 JST9 JBS9 MTX9 JGL9 PAS9; nd_post).
    apply evtF_done. rewrite Z_to_bv_bv_unsigned.
    lazymatch type of MUr with munch ?Wr ?ma ?mb =>
      assert (MUr9 : munch Wr ma m9) by (eapply munch_trans; [exact MUr | eapply munch_weaken; [| exact MU9]; unfold sub_fp; cbn [outside]; clear -CWF; intros q Hq; lia]);
      assert (WMr9 : wmono asegs ma m9) by (eapply wmono_trans; [exact WMr | exact WM9]) end.
    clear MUr WMr. rename MUr9 into MUr. rename WMr9 into WMr.
    carry ZP MUr WMr ltac:(ub DAP; clear -Y SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB NSR NRB0 CWF; dlia).
    carry ZU MUr WMr ltac:(ub DAP; clear -Y SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB NSR NRB0 CWF; dlia).
    carry STATS MUr WMr ltac:(ub DAT; ub DPT; rewrite ?upd_length, ?LSJ; clear -Y Y0 SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB NSR NRB0 CWF T0 T1 PA0 PA0a PA0b PA0c PA0d PA1 TIC; dlia).
    carry POST MUr WMr ltac:(clear -SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB SH1 SH2 SH4 NSR NRB0 CWF PA0 PA0a PA0b PA0c PA0d ASD ASDa ASDb; dlia).   (* [comment removed for export] *)
    carry SHU MUr WMr ltac:(clear -SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB MSR SH1 SH2 SH4 NSR NRB0 CWF PA0 PA0a PA0b PA0c PA0d SZP K0 ASD ASDa ASDb; Z.div_mod_to_equations; dlia).
    carry POST0 MUr WMr ltac:(rewrite SH5; ub MSM; clear -Y SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB MSR SH1 SH2 SH4 NSR NRB0 CWF PA0 PA0a PA0b PA0c PA0d SZP SZ8 K0 ASD ASDa ASDb; Z.div_mod_to_equations; dlia).
    xport ZCR MU9 WM9 ltac:(ub DAP; clear -Y SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB NSR NRB0 CWF PA0 PA0a PA0b PA0c PA0d PA1; dlia).
    assert (MUF : munch [(bv_unsigned sp - LARGE_STACK, bv_unsigned sp); (a, a + ms); (shad a, shad a + ms / 8);
                         (0xab008, 0xab268); (t + 2800, t + 3168);
                         (PA + 8 * nres, PA + 8 * nres + 8); (PA + 8 * nres, PA + 8 * nres + CW)]%Z m m9).
    { eapply munch_trans; [exact MUA|]. eapply munch_weaken; [| exact MU9]. unfold sub_fp. cbn [outside]. clear -MSB CWF. intros q Hq. lia. }
    assert (WMF : wmono asegs m m9) by (eapply wmono_trans; [exact WMA | exact WM9]).
    eapply (KONT2 a RNG'' m9); [exact HFR | reflexivity |].
    unfold large_post. cbv zeta. change (needed_size n) with size. change (sec_map_size n) with ms.
    split; [eapply fp_le_trans; [exact FPLE| exact FPLE2]|]. split; [exact BW2|]. split; [exact AAL|]. split; [exact AHI0|]. split; [atop_facts; exact ACE|].
    split; [eapply munch_weaken; [| exact MUF]; unfold sub_fp, AINSTANCE; cbn [outside]; clear -CWF; intros q Hq; lia|]. split; [exact WMF|]. split; [exact MI9|]. split; [exact ST9|].
    split. { apply (proj2 (rw_cells_app asegs m9 a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 size); C8 (Z_to_bv 64 nres)] [CB _ _])).
             split; [exact ZH9|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. exact ZP. }
    split; [exact ZU|].
    split; [exact POST|]. split; [exact SHU|]. split; [unfold fill_at; rewrite <- SH5; exact POST0|].
    split; [exact RCH|]. split; [exact RSCH|].
    split; [exact INS9|]. split; [exact SRT9|]. split; [exact JST9|]. split; [exact JBS9|]. split; [exact MTX9|]. split; [exact JGL9|].
    split; [eexists; split; [exact STATS| rewrite !upd_length; exact LSJ]|].
    split; [exact PAS9|].
    split; [right; split; [reflexivity|]; split; [reflexivity|]; split; [exact ZCR| exact RPC]|].
    split; [clear -CWF; lia|].
    eapply (large_cells_frame ctx t PA m m9); [exact LC | exact MUF | exact WMF | exact CXI |].
    (nd_pre (tclr_int_lem _ _ DAL ltac:(clear -AHIa; lia) ltac:(clear -AHId; atop_facts; lia)) 4%nat; intros kL DALk DALa DALb; nd_post). (nd_pre (tclr_int_lem _ _ DPL ltac:(clear -PA0a; lia) ltac:(clear -PA0d; atop_facts; lia)) 4%nat; intros kPL DPLk DPLa DPLb; nd_post).      (* [comment removed for export] *)
    ub DAC. ub DPC. ub CT2. unfold AIMG_HI, AIMG_LO. clear -DALk DALa DALb DPLk DPLa DPLb Y Y0 Y1 SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE CX0 CX1 PA0 PA0a PA0b PA0c PA0d PA1 SH1 SH2 MSB T0 T1 NSR NRB0 CWF CXI TIC CBND CBNDa CBNDb TBND TBNDa TBNDb.   (* [comment removed for export] *)
    repeat (apply Forall_cons; [cbn [fst snd]; first [right; lia | left; lia] |]). apply Forall_nil.
  - (* [comment removed for export] *)
    assert (ECW0 : CW = 0) by (ub ECW; destruct (Z.eqb_spec nsec nres) as [E|E]; [exfalso; exact (KQ E) | exact Y]).
    clear CWF. assert (CWF : CW = 0 /\ nres <= 1048576) by (split; [exact ECW0| exact NRB0]).
    specialize (JSL2 ltac:(clear -KQ NSR; lia)).
    xport JSL2 MUq WMq ltac:(ub DAP; clear -Y SPR CEIL LO NSR NRB0 CWF PA0 PA0a PA0b PA0c PA0d PA1 AHI AHIa AHIb AHIc AHId ACE MSB KQ; dlia). clear MUq WMq.
    assert (RPS : rng RNG' (PA + 8 * nsec) 8) by (eapply rng_sub'; [exact RPA|]; clear -KQ NSR; lia).
    eapply evtF_cut.
    { eapply (large_tail_spec RNG' (bv_unsigned sp)); try easm.
      all: try reflexivity.
      all: try (ub DAP; clear -Y CEIL LO SPR NSR NRB0 CWF KQ; lia). }
    cbv beta. intros ms9 PT. unfold large_tail_post in PT.
    (nd_pre PT 16%nat; intros u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m9 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 12%nat; intros MU9 WM9 MI9 ST9 ZH9 INS9 SRT9 JST9 JBS9 MTX9 JGL9 PAS9; nd_post).
    apply evtF_done. rewrite Z_to_bv_bv_unsigned.
    (* [comment removed for export] *)
    lazymatch type of MUr with munch ?Wr ?ma ?mb =>
      assert (MUr9 : munch Wr ma m9) by (eapply munch_trans; [exact MUr | eapply munch_weaken; [| exact MU9]; unfold sub_fp; cbn [outside]; clear -CWF; intros q Hq; lia]);
      assert (WMr9 : wmono asegs ma m9) by (eapply wmono_trans; [exact WMr | exact WM9]) end.
    clear MUr WMr. rename MUr9 into MUr. rename WMr9 into WMr.
    carry ZP MUr WMr ltac:(ub DAP; clear -Y SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB NSR NRB0 CWF; dlia).
    carry ZU MUr WMr ltac:(ub DAP; clear -Y SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB NSR NRB0 CWF; dlia).
    carry STATS MUr WMr ltac:(ub DAT; ub DPT; rewrite ?upd_length, ?LSJ; clear -Y Y0 SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB NSR NRB0 CWF T0 T1 PA0 PA0a PA0b PA0c PA0d PA1 TIC; dlia).
    carry POST MUr WMr ltac:(clear -SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB SH1 SH2 SH4 NSR NRB0 CWF PA0 PA0a PA0b PA0c PA0d ASD ASDa ASDb; dlia).   (* [comment removed for export] *)
    carry SHU MUr WMr ltac:(clear -SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB MSR SH1 SH2 SH4 NSR NRB0 CWF PA0 PA0a PA0b PA0c PA0d SZP K0 ASD ASDa ASDb; Z.div_mod_to_equations; dlia).
    carry POST0 MUr WMr ltac:(rewrite SH5; ub MSM; clear -Y SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB MSR SH1 SH2 SH4 NSR NRB0 CWF PA0 PA0a PA0b PA0c PA0d SZP SZ8 K0 ASD ASDa ASDb; Z.div_mod_to_equations; dlia).
    assert (MUF : munch [(bv_unsigned sp - LARGE_STACK, bv_unsigned sp); (a, a + ms); (shad a, shad a + ms / 8);
                         (0xab008, 0xab268); (t + 2800, t + 3168);
                         (PA + 8 * nsec, PA + 8 * nsec + 8); (PA + 8 * nres, PA + 8 * nres + CW)]%Z m m9).
    { eapply munch_trans; [exact MUA|]. eapply munch_weaken; [| exact MU9]. unfold sub_fp. cbn [outside]. clear -MSB CWF. intros q Hq. lia. }
    assert (WMF : wmono asegs m m9) by (eapply wmono_trans; [exact WMA | exact WM9]).
    eapply (KONT1 a RNG' m9); [exact HFR | exact KQ |].
    unfold large_post. cbv zeta. change (needed_size n) with size. change (sec_map_size n) with ms.
    split; [exact FPLE|]. split; [exact BW|]. split; [exact AAL|]. split; [exact AHI0|]. split; [atop_facts; exact ACE|].
    split; [eapply munch_weaken; [| exact MUF]; unfold sub_fp, AINSTANCE; cbn [outside]; clear -CWF; intros q Hq; lia|]. split; [exact WMF|]. split; [exact MI9|]. split; [exact ST9|].
    split. { apply (proj2 (rw_cells_app asegs m9 a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 size); C8 (Z_to_bv 64 nsec)] [CB _ _])).
             split; [exact ZH9|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. exact ZP. }
    split; [exact ZU|].
    split; [exact POST|]. split; [exact SHU|]. split; [unfold fill_at; rewrite <- SH5; exact POST0|].
    split; [exact RCH|]. split; [exact RSCH|].
    split; [exact INS9|]. split; [exact SRT9|]. split; [exact JST9|]. split; [exact JBS9|]. split; [exact MTX9|]. split; [exact JGL9|].
    split; [eexists; split; [exact STATS| rewrite !upd_length; exact LSJ]|].
    split; [exact PAS9|].
    split; [left; split; [exact KQ| reflexivity]|].
    split; [exact NRB0|].
    eapply (large_cells_frame ctx t PA m m9); [exact LC | exact MUF | exact WMF | exact CXI |].
    (nd_pre (tclr_int_lem _ _ DAL ltac:(clear -AHIa; lia) ltac:(clear -AHId; atop_facts; lia)) 4%nat; intros kL DALk DALa DALb; nd_post). (nd_pre (tclr_int_lem _ _ DPL ltac:(clear -PA0a; lia) ltac:(clear -PA0d; atop_facts; lia)) 4%nat; intros kPL DPLk DPLa DPLb; nd_post).      (* [comment removed for export] *)
    ub DAC. ub DPC. ub CT2. unfold AIMG_HI, AIMG_LO. clear -DALk DALa DALb DPLk DPLa DPLb Y Y0 Y1 SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE CX0 CX1 PA0 PA0a PA0b PA0c PA0d PA1 SH1 SH2 MSB T0 T1 NSR NRB0 CWF CXI TIC CBND CBNDa CBNDb TBND TBNDa TBNDb.   (* [comment removed for export] *)
    repeat (apply Forall_cons; [cbn [fst snd]; first [right; lia | left; lia] |]). apply Forall_nil.
  Unshelve. all: try (apply ref_ro_addr_false; right; lia).
Qed.
End Zd2.
#[using="Type"] Lemma large_spec : forall RNG {R} (K : Z -> itree node (exc R)) (K2 : Z -> Z -> itree node (exc R))
    (Q : R -> footprint -> machine_state -> Prop) (FRESH : Z -> bool)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n ctx t PA nres nsec lo : Z) (sj : list word) (sorted : Z) (jstats jbsl jglob jslot : list byte),
  let size := needed_size n in let ms := sec_map_size n in
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - LARGE_STACK ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 0xaafd8 -> a1 = Z_to_bv 64 0xab248 ->      (* [comment removed for export] *) a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 8 ->
  1 <= n <= AREQMAX -> is_primary n = false ->
  large_cells ctx t PA m ->
  (* [comment removed for export] *)
  sclr ctx 65536 -> ctx + 4096 <= ATOP -> sclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  (* [comment removed for export] *)
  rw_cells asegs m 0xab008 [C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 nsec)] ->
  rw_cells asegs m 0xab018 [C1 (Z_to_bv 8 sorted)] ->
  rw_cells asegs m 0xab020 [CB 32 jstats] ->
  rw_cells asegs m 0xab040 [CB 512 jbsl] ->
  rw_cells asegs m 0xab240 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m 0xab258 [CB 16 jglob] ->
  (* [comment removed for export] *)
  ablk PA (PA + 8388608) -> PA + 8388608 <= ATOP -> PA mod 4096 = 0 ->      (* [comment removed for export] *)
  0 <= nsec <= nres -> nres mod 16384 = 0 -> nres <= 1048576 ->
  (nsec < nres -> rw_cells asegs m (PA + 8 * nsec) [CB 8 jslot]) ->
  (PA + 8388608 <= t \/ t + 4096 <= PA) -> (PA + 8388608 <= ctx \/ ctx + 4096 <= PA) ->
  tclr PA 8388608 ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG PA (8 * nres) ->
  AIMG_HI <= ctx -> iclr t 4096 ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  (forall a, FRESH a = true ->
        ablk a (a + ms)
     /\ (a + ms <= t \/ t + 4096 <= a) /\ (a + ms <= ctx \/ ctx + 4096 <= a) /\ (a + ms <= PA \/ PA + 8388608 <= a)
     /\ fill_at m (shad a) (ms / 8) 0
     /\ tclr a ms) ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  (forall a RNG' ms', FRESH a = false -> 0 < a -> a mod 4096 = 0 -> a + ms <= ATOP -> fp_le RNG RNG' ->
      implS asegs RNG' (K a) (epostF Q) ms') ->
  (* [comment removed for export] *)
  (forall a RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      FRESH a = true -> nsec <> nres -> large_post RNG sp a n ctx t PA nres nsec nres lo m RNG' m' ->
      implS asegs RNG' (K a) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (a + 4096)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  (* [comment removed for export] *)
  (forall a, FRESH a = true -> nsec = nres -> nres + 16384 <= 1048576 ->
      K a = ebind (enode (NMmap (PA + 8 * nres) 131072 3 50) (adec_mmap ATOP 131072 3)) (K2 a)) ->
  (* [comment removed for export] *)
  (forall a RNG' ms', FRESH a = true -> nsec = nres -> 1048576 < nres + 16384 -> implS asegs RNG' (K a) (epostF Q) ms') ->
  (forall a r RNG' ms', r <> PA + 8 * nres -> 0 < r -> r + 131072 <= ATOP -> implS asegs RNG' (K2 a r) (epostF Q) ms') ->
  (forall a RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      FRESH a = true -> nsec = nres -> large_post RNG sp a n ctx t PA nres nsec (nres + 16384) lo m RNG' m' ->
      implS asegs RNG' (K2 a (PA + 8 * nres)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (a + 4096)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (ebind (enode (NMmap 0 ms 3 34) (adec_mmap ATOP ms 3)) K) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 large_entry) fc None m (seg_rom asegs)).
Proof. exact large_spec__body. Qed.
End CANSEC2.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MM_syscalls.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.ASecSlog.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.RT_stubs.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memchr__A3W.F_memset.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison0.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acache3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_ammap.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_iseg__A3W.F_ammapz.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From Ltac2 Require Import Ltac2.
Local Ltac2 rec zt_skel (cs : constant FSet.t) (t : constr) : bool :=
  if zt_plain_arith_s cs t then true else
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      if lt_is_ref h reference:(or) then (if zt_skel cs (Array.get args 0) then zt_skel cs (Array.get args 1) else false)
      else if lt_is_ref h reference:(and) then (if zt_skel cs (Array.get args 0) then zt_skel cs (Array.get args 1) else false)
      else if lt_is_ref h reference:(not) then zt_skel cs (Array.get args 0)
      else if lt_is_ref h reference:(iff) then (if zt_skel cs (Array.get args 0) then zt_skel cs (Array.get args 1) else false)
      else false
  | Constr.Unsafe.Prod b c =>
      if Constr.Unsafe.noccurn 1 c then (if zt_skel cs (Constr.Binder.type b) then zt_skel cs c else false) else false
  | _ => false
  end.
Local Ltac2 zt_prune_keepor () : unit :=
  let hs := Control.hyps () in
  let cs := zt_plain_consts () in
  let extra := List.exist (fun h => let (id, body, ty) := h in
                 match body with
                 | Some _ => false
                 | None => if zt_is_local id then (if zt_plain_arith_s cs ty then false else zt_skel cs ty) else false
                 end) hs in
  if extra then
    let ids := List.map_filter (fun h => let (id, body, ty) := h in
                  match body with
                  | Some _ => None
                  | None => if zt_skel cs ty then None else if zt_is_local id then zt_is_prop_some ty id else None
                  end) hs in
    match ids with [] => () | _ :: _ => Std.clear ids end
  else Control.zero (Tactic_failure None).
Local Ltac zify_prune_keepor := ltac2:(Control.enter zt_prune_keepor).
Set Default Proof Mode "Classic".
Local Ltac Stdlib.micromega.Lia.lia ::=
  first [ zify_prune; first [ zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                            | Zify.zify; xlia zchecker ]
        | zify_prune_keepor; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
Local Ltac zrange_gz_g :=
  lazymatch goal with
  | |- inr64 (Z.sub (cb_sm _) (Z.land (Z.shiftr (cb_sm _) (1)%Z) (6148914691236517205)%Z)) => fail   (* [comment removed for export] *)
  | |- inr64 (Z.add (Z.b2z (Z.ltb _ _)) (-1)%Z) => fail   (* [comment removed for export] *)
  | |- inr64 (Z.sub (0)%Z (Z.b2z (Z.ltb _ _))) => fail   (* [comment removed for export] *)
  (* [comment removed for export] *)
  | |- inr64 (Z.add (Z.land _ (3689348814741910323)%Z) (Z.land (Z.shiftr _ (2)%Z) (3689348814741910323)%Z)) => fail   (* [comment removed for export] *)
  | |- inr64 (Z.add (Z.add (Z.land _ (3689348814741910323)%Z) (Z.land (Z.shiftr _ (2)%Z) (3689348814741910323)%Z)) (Z.shiftr _ (4)%Z)) => fail   (* [comment removed for export] *)
  | |- inr64 (Z.mul (Z.land _ (1085102592571150095)%Z) (72340172838076673)%Z) => fail   (* [comment removed for export] *)
  | |- _ => zrange
  end.
Local Ltac zrange_gz_i :=
  lazymatch goal with
  | |- inr64 (Z.add (bv_unsigned _) _) => fail   (* [comment removed for export] *)
  | |- _ => zrange
  end.
Local Ltac zsimp ::=
  rewrite ?v_sltu_b2z, ?v_slt_b2z, ?v_sltiu_b2z, ?v_slti_b2z;
  cbv delta [zxb];
  zb_fold_lits;
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?e)] =>
      first [ rewrite (inr64_unsigned_lit e) by zrange_gz_g
            | zs_wrap e ]            (* [comment removed for export] *)
  | |- _ => progress zs_idioms
  end; zb_fold_lits.
Local Ltac zsimp_in H ::=
  rewrite ?v_sltu_b2z, ?v_slt_b2z, ?v_sltiu_b2z, ?v_slti_b2z in H;
  cbv delta [zxb] in H;
  zb_fold_lits_in H;
  repeat match type of H with
  | context [bv_unsigned (Z_to_bv 64 ?e)] =>
      first [ rewrite (inr64_unsigned_lit e) in H by zrange_gz_i
            | zs_wrap_in e H ]
  | _ => progress (zs_idioms_in H)
  end; zb_fold_lits_in H.
Local Ltac d_is_natlit n ::= sl_is_natlit n.
Local Ltac is_natlit n ::= sl_is_natlit n.
Local Ltac flia ::= first [ sassumption | clear; lia | slim; lia | lia | assumption ].   (* [comment removed for export] *)
Import ListNotations.
Import Exc.
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
Local Ltac fp_cheap8 := first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs end | clear ]; Stdlib.micromega.Lia.lia.   (* [comment removed for export] *)
Local Ltac fp_find8c := first [ apply Exists_cons_hd; cbn [fst snd]; split; fp_cheap8 | apply Exists_cons_tl; fp_find8c ].
Local Ltac fp_find8 := first [ apply Exists_cons_hd; cbn [fst snd]; split; lia | apply Exists_cons_tl; fp_find8 ].
Local Ltac fp_cover8 := apply sub_fp_cover8; repeat (apply Forall_cons; [ cbn [fst snd]; first [left; fp_cheap8 | right; fp_find8c | right; fp_find8] | ]); apply Forall_nil.
(* [comment removed for export] *)
Local Ltac transport_call_munch_tac ::= first [ fp_cover8 | unfold sub_fp; cbn [outside]; first [ match goal with Hs : bv_unsigned _ = bv_unsigned _ + _ |- _ => clear -Hs; intros; lia end | clear; intros; lia | intros; slia ] ].
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac dlia := repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

Local Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.
(* [comment removed for export] *)
Local Ltac easm := first [ lazymatch goal with |- rw_cells ?s ?mm ?A _ => match goal with H : rw_cells s mm A _ |- _ => exact H end end | eassumption ].
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
Definition large_entry := 0x386c8.
End CANSEC1.
Notation LARGE_STACK := 464 (only parsing).   (* [comment removed for export] *)

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
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
Definition large_cells (ctx t PA : Z) (m : amem) : Prop :=
     rmap_cells m /\ poison_cells m
  /\ rw_cells asegs m 0xa5878 [C8 (Z_to_bv 64 0xa7778)] /\ rw_cells asegs m 0xa7778 [C8 (Z_to_bv 64 0x19361)]
  /\ rw_cells asegs m 0xae260 [C1 (Z_to_bv 8 1)] /\ rw_cells asegs m 0xae264 [C4 (Z_to_bv 64 0)]
  /\ rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] /\ rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)]
  /\ rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)]
  /\ rw_cells asegs m 0xab3d8 [C8 (Z_to_bv 64 4096); C8 (Z_to_bv 64 PA); C8 (Z_to_bv 64 PA)].      (* [comment removed for export] *)

#[using="Type"] Lemma large_cells_frame : forall ctx t PA m m' W, large_cells ctx t PA m -> munch W m m' -> wmono asegs m m' ->
  AIMG_HI <= ctx ->
  Forall (fun iv => (((snd iv <= AIMG_LO \/ AIMG_HI <= fst iv) /\ (snd iv <= ATPv + -88 \/ ATPv + -80 <= fst iv)) /\ (snd iv <= ctx + 152 \/ ctx + 160 <= fst iv))      (* [comment removed for export] *)
                    \/ (0xab3f0 <= fst iv /\ snd iv <= 0xadc00)) W -> large_cells ctx t PA m'.
Proof.
  intros ctx t PA m m' W LC MU WM CX HW.
  (nd_pre LC 10%nat; intros (Q1 & Q2 & Q3 & Q4 & Q5) (P1 & P2 & P3 & P4 & P5 & P6 & P7) R3 R4 R5 R6 R7 R8 R9 R10; nd_post).
  unfold AIMG_HI, AIMG_LO, ATP88, ATSD in *.
  assert (D : forall A k, 0 <= k -> ((0x10000 <= A /\ A + k <= 0xab3f0) \/ (0xadc00 <= A /\ A + k <= 0x604000) \/ (A = ctx + 152 /\ k = 8) \/ (A = ATPv + -88 /\ k = 8)) -> disjoint_from W A k).      (* [comment removed for export] *)
  { pose proof atp_lin as TLN. clear -HW CX TLN. intros A k Hk HA. induction W as [|[lo hi] W IH]; cbn; [exact I|]. inversion HW; subst. cbn in *. split; [lia| apply IH; assumption]. }      (* [comment removed for export] *)
  unfold large_cells, rmap_cells, poison_cells. repeat lazymatch goal with |- _ /\ _ => split end;
    (eapply rw_cells_transport; [eassumption | exact MU | exact WM | unfold ATP88, ATSD; cbn; apply D; lia]).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma zeros32_hdr : forall m A, fill_at m A 32 0 ->
  rw_cells asegs m A [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
Proof. intros m A H. eapply rw_cells_recast; [exact H | cbn; tauto | vm_compute; reflexivity | reflexivity]. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma mtx_to_C4 : forall m (b : Z), 0 <= b < 256 ->
  rw_cells asegs m 0xab640 [C1 (Z_to_bv 8 b); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m 0xab640 [C4 (Z_to_bv 64 b)].
Proof.
  intros m b Hb H. eapply rw_cells_recast; [exact H | cbn; tauto | | reflexivity].
  cbn [cells_bytes cbytes app]. replace b with (b + 256 * 0) at 1 by lia. rewrite (le4_two_bytes b 0) by lia. reflexivity.
Qed.
#[using="Type"] Lemma mtx_of_C4 : forall m (b : Z), 0 <= b < 256 ->
  rw_cells asegs m 0xab640 [C4 (Z_to_bv 64 b)] ->
  rw_cells asegs m 0xab640 [C1 (Z_to_bv 8 b); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Proof.
  intros m b Hb H. eapply rw_cells_recast; [exact H | cbn; tauto | | reflexivity].
  cbn [cells_bytes cbytes app]. replace b with (b + 256 * 0) at 2 by lia. rewrite (le4_two_bytes b 0) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Definition large_post (RNG : footprint) (sp : word) (a n ctx t PA nres nsec nres' lo : Z) (m : amem)
    (RNG' : footprint) (m' : amem) : Prop :=
  let size := needed_size n in let ms := sec_map_size n in let res := a + 4096 in let ue := res + size in
     fp_le RNG RNG' /\ fp_bw RNG'
  /\ a mod 4096 = 0 /\ ablk a (a + ms) /\ a + ms <= ATOP            (* [comment removed for export] *)
  /\ munch [(bv_unsigned sp - LARGE_STACK, bv_unsigned sp); (a, a + ms); (shad a, shad a + ms / 8);
            (AINSTANCE + 112, AINSTANCE + 720); (t + 2800, t + 3168);
            (PA + 8 * nsec, PA + 8 * nsec + 8); (PA + 8 * nres, PA + 8 * nres')]%Z m m'
  /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
     (* [comment removed for export] *)
  /\ rw_cells asegs m' a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 size); C8 (Z_to_bv 64 nsec);
                          CB (Z.to_nat (4096 - 32)) (repeat (Z_to_bv 8 0) (Z.to_nat (4096 - 32)))]
  /\ rw_cells asegs m' res [CB (Z.to_nat (ms - 4096)) (repeat (Z_to_bv 8 0) (Z.to_nat (ms - 4096)))]
  /\ fill_at m' (shad a) 512 0xfa
  /\ fill_at m' (shad a + 512) (size / 8) 0
  /\ fill_at m' (shad a + 512 + size / 8) (ms / 8 - 512 - size / 8) 0xfa
  /\ rng RNG' a ms /\ rng RNG' (shad a) (ms / 8)
     (* [comment removed for export] *)
  /\ rw_cells asegs m' 0xab408 [C8 (Z_to_bv 64 nres'); C8 (Z_to_bv 64 (nsec + 1))]
  /\ rw_cells asegs m' 0xab418 [C1 (Z_to_bv 8 0)]
  /\ junk_at m' 0xab420 32 /\ junk_at m' 0xab440 512
  /\ rw_cells asegs m' 0xab640 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
  /\ junk_at m' 0xab658 16
  /\ (exists sj', u64arr asegs m' (t + 2800) sj' /\ length sj' = 46%nat)
  /\ rw_cells asegs m' (PA + 8 * nsec) [C8 (Z_to_bv 64 a)]
  /\ ((nsec <> nres /\ nres' = nres)
      \/ (nsec = nres /\ nres' = nres + 16384
          /\ rw_cells asegs m' (PA + 8 * nres + 8) [CB (Z.to_nat (131072 - 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (131072 - 8)))]
          /\ rng RNG' (PA + 8 * nres) 131072))
  /\ nres' <= 1048576
  /\ large_cells ctx t PA m'.

(* [comment removed for export] *)
#[using="Type"] Lemma c8x4_of_junk : forall m A, junk_at m A 32 -> exists w1 w2 w3 w4 : word, rw_cells asegs m A [C8 w1; C8 w2; C8 w3; C8 w4].
Proof.
  intros m A J. destruct (junk_split m A 16 16 J ltac:(lia) ltac:(lia)) as [J1 J2].
  (nd_pre (c8c8_of_junk m A J1) 3%nat; intros w1 w2 H1; nd_post). (nd_pre (c8c8_of_junk m (A + 16) J2) 3%nat; intros w3 w4 H2; nd_post).
  exists w1, w2, w3, w4. apply (proj2 (rw_cells_app asegs m A [C8 w1; C8 w2] [C8 w3; C8 w4])). split; [exact H1| exact H2].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma lxor63 : forall k, 0 <= k <= 63 -> Z.lxor k 63 = 63 - k.
Proof.
  apply (range_by_compute (fun k => Z.lxor k 63 = 63 - k) (fun k => Z.lxor k 63 =? 63 - k) 0 63); [| vm_compute; reflexivity].
  intros z Hz. apply Z.eqb_eq. exact Hz.
Qed.

(* [comment removed for export] *)
Definition large_tail_post (sp0 : Z) (vra v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 s10v s11v gp tp a0 : word) (F : bvmap 5 word) (fc : bv 32)
    (a ms size PA nres' nsec lo : Z) (fj : list byte) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR vra (Z_to_bv 64 sp0) gp tp t0 t1 t2 v0 v1 a0 a1 a2 a3 a4 a5 a6 a7 v2 v3 v4 v5 v6 v7 v8 v9 s10v s11v t3 t4 t5 t6)
             F (ret_pc vra) fc None m' (seg_rom asegs)
    /\ munch [(sp0 - 96, sp0); (a + 24, a + 32); (0xab408, 0xab668); (PA + 8 * nsec, PA + 8 * nsec + 8)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo sp0
    /\ rw_cells asegs m' a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 size); C8 (Z_to_bv 64 nsec)]
    /\ rw_cells asegs m' 0xab408 [C8 (Z_to_bv 64 nres'); C8 (Z_to_bv 64 (nsec + 1))]
    /\ rw_cells asegs m' 0xab418 [C1 (Z_to_bv 8 0)]
    /\ junk_at m' 0xab420 32 /\ junk_at m' 0xab440 512
    /\ rw_cells asegs m' 0xab640 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ junk_at m' 0xab658 16
    /\ rw_cells asegs m' (PA + 8 * nsec) [C8 (Z_to_bv 64 a)].

Definition large_tail_spec__stmt : Prop := forall RNG (sp0 : Z) (vra v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 s10v s11v : word)
    ra gp tp t0 t1 t2 a0 a1 a2 a4 a5 a6 a7 s4 s6 s7 s8 s9 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (a ms size PA nres' nsec k lo : Z) (srt : byte) (fj jstats jbsl jglob jslot : list byte),
  stk asegs m lo (sp0 - 96) -> ATOP <= lo -> lo <= sp0 - 96 -> sp0 < 2^64 ->
  mem_inv asegs m ->
  rw_cells asegs m (sp0 + -96) [CB 8 fj; C8 v9; C8 v8; C8 v7; C8 v6; C8 v5; C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 vra] ->
  rw_cells asegs m 0xab3d8 [C8 (Z_to_bv 64 4096); C8 (Z_to_bv 64 PA); C8 (Z_to_bv 64 PA)] ->
  rw_cells asegs m a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 size); C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m 0xab408 [C8 (Z_to_bv 64 nres'); C8 (Z_to_bv 64 nsec)] ->
  rw_cells asegs m 0xab418 [C1 srt] ->
  rw_cells asegs m 0xab420 [CB 32 jstats] -> rw_cells asegs m 0xab440 [CB 512 jbsl] ->
  rw_cells asegs m 0xab640 [C4 (Z_to_bv 64 1)] ->
  rw_cells asegs m 0xab658 [CB 16 jglob] ->
  rw_cells asegs m (PA + 8 * nsec) [CB 8 jslot] ->
  ablk a (a + ms) -> a + ms <= ATOP -> (a + ms <= PA \/ PA + 8388608 <= a) ->
  ablk PA (PA + 8388608) -> PA + 8388608 <= ATOP -> 0 <= nsec -> 8 * nsec + 8 <= 8388608 -> 0 <= nres' < 2^64 ->
  73728 <= ms <= 536821760 -> 34 <= k <= 47 ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (sp0 - lo) -> rng RNG a ms -> rng RNG (PA + 8 * nsec) 8 ->
  evtF asegs RNG (large_tail_post sp0 vra v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 s10v s11v gp tp a0 F fc a ms size PA nres' nsec lo fj m)
    (MS (mkR ra (Z_to_bv 64 (sp0 + -96)) gp tp t0 t1 t2 (Z_to_bv 64 0xab648) (Z_to_bv 64 0xab3d8) a0 a1 a2 (Z_to_bv 64 nsec) a4 a5 a6 a7
             (Z_to_bv 64 ms) (Z_to_bv 64 k) s4 (Z_to_bv 64 a) s6 s7 s8 s9 s10v s11v t3 t4 t5 t6)
        F (Z_to_bv 64 0x3892c) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 0).
Variable sp0 : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 1).
Variable vra : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 2).
Variable v0 : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 3).
Variable v1 : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 4).
Variable v2 : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 5).
Variable v3 : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 6).
Variable v4 : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 7).
Variable v5 : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 8).
Variable v6 : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 9).
Variable v7 : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 10).
Variable v8 : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 11).
Variable v9 : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 12).
Variable s10v : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 13).
Variable s11v : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 14).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 15).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 16).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 17).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 18).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 19).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 20).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 21).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 22).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 23).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 24).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 25).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 26).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 27).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 28).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 29).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 30).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 31).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 32).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 33).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 34).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 35).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 36).
Variable F : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 37).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 38).
Variable m : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 39).
Variable a : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 40).
Variable ms : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 41).
Variable size : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 42).
Variable PA : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 43).
Variable nres' : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 44).
Variable nsec : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 45).
Variable k : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 46).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 47).
Variable srt : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 48).
Variable fj : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 49).
Variable jstats : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 50).
Variable jbsl : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 51).
Variable jglob : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 52).
Variable jslot : ltac2:(SecDietF.SzSecF.ty 'large_tail_spec__stmt 53).
#[using="Type"] Lemma large_tail_spec__body : ltac:(let T := type of (fun (h : large_tail_spec__stmt) => h RNG sp0 vra v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 s10v s11v ra gp tp t0 t1 t2 a0 a1 a2 a4 a5 a6 a7 s4 s6 s7 s8 s9 t3 t4 t5 t6 F fc m a ms size PA nres' nsec k lo srt fj jstats jbsl jglob jslot) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (sp0, (vra, (v0, (v1, (v2, (v3, (v4, (v5, (v6, (v7, (v8, (v9, (s10v, (s11v, (ra, (gp, (tp, (t0, (t1, (t2, (a0, (a1, (a2, (a4, (a5, (a6, (a7, (s4, (s6, (s7, (s8, (s9, (t3, (t4, (t5, (t6, (F, (fc, (m, (a, (ms, (size, (PA, (nres', (nsec, (k, (lo, (srt, (fj, (jstats, (jbsl, (jglob, jslot)))))))))))))))))))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO SP64 MI FR I64 ZH INS SRT JST JBS MTX JGL JSL AHI ACE DAP PA0 PA1 NS0 NS1 NR MSB KB RIMG RTLS RSTK RCH RPS.
  pose proof AHI as AHI0. pose proof PA0 as PA00. clear AHI PA0. (nd_pre (ablk_int _ _ AHI0) 6%nat; intros kA AHI AHIa AHIb AHIc AHId; nd_post). (nd_pre (ablk_int _ _ PA00) 6%nat; intros kP PA0 PA0a PA0b PA0c PA0d; nd_post).   (* [comment removed for export] *)
  atop_facts.
  pose proof (munch_refl [(sp0 - 96, sp0); (a + 24, a + 32); (0xab408, 0xab668); (PA + 8 * nsec, PA + 8 * nsec + 8)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  box DAP.
  destruct (c8_of_junk m (PA + 8 * nsec) (ex_intro _ jslot JSL)) as [wj PAS]. clear JSL.
  step.                                                        (* [comment removed for export] *)
  zstep. rewrite (lxor63 k) by (clear -KB; lia).               (* [comment removed for export] *)
  box PAS. snapshot [(a + 24, a + 32)]%Z MUh WMh.
  step.                                                        (* [comment removed for export] *)
  carry PAS MUh WMh ltac:(ub DAP; clear -Y NS0 NS1 AHI AHIa AHIb AHIc AHId MSB; dlia). clear MUh WMh.
  zstep. zstep.                                                (* [comment removed for export] *)
  setreg 12 (Z_to_bv 64 (PA + 8 * nsec)) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by (clear; lia); clear -NS0 NS1; lia).
  box ZH. snapshot [(PA + 8 * nsec, PA + 8 * nsec + 8)]%Z MUp WMp.
  remember (PA + 8 * nsec) as PS eqn:HPS.
  step.                                                        (* [comment removed for export] *)
  subst PS.
  carry ZH MUp WMp ltac:(ub DAP; clear -Y NS0 NS1 AHI AHIa AHIb AHIc AHId MSB; dlia). clear MUp WMp.
  (* [comment removed for export] *)
  (nd_pre (c8x4_of_junk _ 0xab420 (ex_intro _ jstats JST)) 5%nat; intros w1 w2 w3 w4 AST; nd_post). clear JST.
  step. step.                                                  (* [comment removed for export] *)
  zstep.                                                       (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  zstep. zstep.                                                (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  (* [comment removed for export] *)
  destruct (junk_split _ 0xab440 (8 * (63 - k)) (512 - 8 * (63 - k)) ltac:(replace (8 * (63 - k) + (512 - 8 * (63 - k))) with 512 by (clear; lia); exists jbsl; exact JBS)
              ltac:(clear -KB; lia) ltac:(clear -KB; lia)) as [JB1 JB2].
  destruct (junk_split _ (0xab440 + 8 * (63 - k)) 8 (512 - 8 * (63 - k) - 8) ltac:(replace (8 + (512 - 8 * (63 - k) - 8)) with (512 - 8 * (63 - k)) by (clear; lia); exact JB2)
              ltac:(clear; lia) ltac:(clear -KB; lia)) as [JBW JB3]. clear JB2 JBS.
  destruct (c8_of_junk _ _ JBW) as [wb BSL]. clear JBW. destruct JB1 as [bs1 JB1]. destruct JB3 as [bs3 JB3].
  remember (0xab3d8 + 8 * (63 - k)) as BSB eqn:HBSB.
  replace (0xab440 + 8 * (63 - k)) with (BSB + 104) in BSL by (subst BSB; clear; lia).
  replace (0xab440 + 8 * (63 - k) + 8) with (BSB + 112) in JB3 by (subst BSB; clear; lia).
  step. if_cases KM; zify_cond KM.
  all: try lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x38970) _ _ _ _) => step end.   (* [comment removed for export] *)
  all: zstep; zstep.                                           (* [comment removed for export] *)
  all: setreg 11 (Z_to_bv 64 BSB) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by (clear; lia); subst BSB; clear -KB; lia).
  all: step.                                                   (* [comment removed for export] *)
  all: zstep.                                                  (* [comment removed for export] *)
  all: step; step.                                             (* [comment removed for export] *)
  (* [comment removed for export] *)
  all: (nd_pre (c8c8_of_junk _ 0xab658 (ex_intro _ jglob JGL)) 3%nat; intros g0 g1 GL; nd_post); clear JGL.
  all: zstep.                                                  (* [comment removed for export] *)
  all: assert (AMO1 : amo_aligned AD (Z_to_bv 64 0xab658) = true) by (apply amo_alignedD_intro; [clear; lia| reflexivity]).
  all: amo_stepA AMO1.                                         (* [comment removed for export] *)
  all: zstep.                                                  (* [comment removed for export] *)
  all: assert (AMO2 : amo_aligned AD (Z_to_bv 64 0xab660) = true) by (apply amo_alignedD_intro; [clear; lia| reflexivity]).
  all: amo_stepA AMO2.                                         (* [comment removed for export] *)
  all: step.                                                   (* [comment removed for export] *)
  (* [comment removed for export] *)
  all: apply (mtx_of_C4 _ 1 ltac:(clear; lia)) in MTX.
  all: step.                                                   (* [comment removed for export] *)
  (* [comment removed for export] *)
  all: do 13 step.                                             (* [comment removed for export] *)
  all: lazymatch goal with FRM : rw_cells asegs ?mm (?spz + -96) (CB 8 _ :: _) |- _ => lazymatch goal with STK : stk asegs mm ?loz _ |- _ => release_frame FRM STK spz end end.
  all: apply evtF_done; unfold large_tail_post; do 15 eexists; split; [reflexivity|].
  all: split; [assumption|]. all: split; [assumption|]. all: split; [assumption|]. all: split; [assumption|].
  all: split; [exact ZH|]. all: split; [assumption|]. all: split; [assumption|].
  all: split; [exact (junk_of_cells _ _ _ AST)|].
  all: split.
  1,3: subst BSB; replace 512 with (8 * (63 - k) + (512 - 8 * (63 - k))) by (clear; lia);
       apply junk_merge; [exists bs1; exact JB1 | | clear -KB; lia| clear -KB; lia];
       replace (512 - 8 * (63 - k)) with (8 + (512 - 8 * (63 - k) - 8)) by (clear; lia);
       apply junk_merge; [ | | clear; lia | clear -KB; lia];
       [ replace (701504 + 8 * (63 - k)) with (701400 + 8 * (63 - k) + 104) by (clear; lia); exact (junk_of_cells _ _ _ BSL)
       | replace (701504 + 8 * (63 - k) + 8) with (701400 + 8 * (63 - k) + 112) by (clear; lia); exists bs3; exact JB3 ].
  all: split; [assumption|]. all: split; [| assumption].
  all: exact (junk_of_cells _ _ _ GL).
  Unshelve. all: try (apply ref_ro_addr_false; right; lia).
Qed.
End Zd1.
#[using="Type"] Lemma large_tail_spec : ltac:(let t := eval cbv delta [large_tail_spec__stmt] in large_tail_spec__stmt in exact t).
Proof. exact large_tail_spec__body. Qed.

Definition large_spec__stmt : Prop := forall RNG {R} (K : Z -> itree node (exc R)) (K2 : Z -> Z -> itree node (exc R))
    (Q : R -> footprint -> machine_state -> Prop) (FRESH : Z -> bool)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n ctx t PA nres nsec lo : Z) (sj : list word) (sorted : Z) (jstats jbsl jglob jslot : list byte),
  let size := needed_size n in let ms := sec_map_size n in
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - LARGE_STACK ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 0xab3d8 -> a1 = Z_to_bv 64 0xab648 ->      (* [comment removed for export] *) a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 8 ->
  1 <= n <= AREQMAX -> is_primary n = false ->
  large_cells ctx t PA m ->
  (* [comment removed for export] *)
  sclr ctx 65536 -> ctx + 4096 <= ATOP -> sclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  (* [comment removed for export] *)
  rw_cells asegs m 0xab408 [C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 nsec)] ->
  rw_cells asegs m 0xab418 [C1 (Z_to_bv 8 sorted)] ->
  rw_cells asegs m 0xab420 [CB 32 jstats] ->
  rw_cells asegs m 0xab440 [CB 512 jbsl] ->
  rw_cells asegs m 0xab640 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m 0xab658 [CB 16 jglob] ->
  (* [comment removed for export] *)
  ablk PA (PA + 8388608) -> PA + 8388608 <= ATOP -> PA mod 4096 = 0 ->      (* [comment removed for export] *)
  0 <= nsec <= nres -> nres mod 16384 = 0 -> nres <= 1048576 ->
  (nsec < nres -> rw_cells asegs m (PA + 8 * nsec) [CB 8 jslot]) ->
  (PA + 8388608 <= t \/ t + 4096 <= PA) -> (PA + 8388608 <= ctx \/ ctx + 4096 <= PA) ->
  tclr PA 8388608 ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG PA (8 * nres) ->
  AIMG_HI <= ctx -> iclr t 4096 ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  (forall a, FRESH a = true ->
        ablk a (a + ms)
     /\ (a + ms <= t \/ t + 4096 <= a) /\ (a + ms <= ctx \/ ctx + 4096 <= a) /\ (a + ms <= PA \/ PA + 8388608 <= a)
     /\ fill_at m (shad a) (ms / 8) 0
     /\ tclr a ms) ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  (forall a RNG' ms', FRESH a = false -> 0 < a -> a mod 4096 = 0 -> a + ms <= ATOP -> fp_le RNG RNG' ->
      implS asegs RNG' (K a) (epostF Q) ms') ->
  (* [comment removed for export] *)
  (forall a RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      FRESH a = true -> nsec <> nres -> large_post RNG sp a n ctx t PA nres nsec nres lo m RNG' m' ->
      implS asegs RNG' (K a) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (a + 4096)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  (* [comment removed for export] *)
  (forall a, FRESH a = true -> nsec = nres -> nres + 16384 <= 1048576 ->
      K a = ebind (enode (NMmap (PA + 8 * nres) 131072 3 50) (adec_mmap ATOP 131072 3)) (K2 a)) ->
  (* [comment removed for export] *)
  (forall a RNG' ms', FRESH a = true -> nsec = nres -> 1048576 < nres + 16384 -> implS asegs RNG' (K a) (epostF Q) ms') ->
  (forall a r RNG' ms', r <> PA + 8 * nres -> 0 < r -> r + 131072 <= ATOP -> implS asegs RNG' (K2 a r) (epostF Q) ms') ->
  (forall a RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      FRESH a = true -> nsec = nres -> large_post RNG sp a n ctx t PA nres nsec (nres + 16384) lo m RNG' m' ->
      implS asegs RNG' (K2 a (PA + 8 * nres)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (a + 4096)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (ebind (enode (NMmap 0 ms 3 34) (adec_mmap ATOP ms 3)) K) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 large_entry) fc None m (seg_rom asegs)).
Section Zd2.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 0).
Variable R : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 1).
Variable K : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 2).
Variable K2 : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 3).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 4).
Variable FRESH : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 5).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 6).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 7).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 8).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 9).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 10).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 11).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 12).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 13).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 14).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 15).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 16).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 17).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 18).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 19).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 20).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 21).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 22).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 23).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 24).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 25).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 26).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 27).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 28).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 29).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 30).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 31).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 32).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 33).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 34).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 35).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 36).
Variable F : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 37).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 38).
Variable m : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 39).
Variable n : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 40).
Variable ctx : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 41).
Variable t : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 42).
Variable PA : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 43).
Variable nres : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 44).
Variable nsec : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 45).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 46).
Variable sj : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 47).
Variable sorted : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 48).
Variable jstats : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 49).
Variable jbsl : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 50).
Variable jglob : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 51).
Variable jslot : ltac2:(SecDietF.SzSecF.ty 'large_spec__stmt 52).
Let size := needed_size n.
Let ms := sec_map_size n.
#[using="size ms"] Lemma large_spec__body : ltac:(let T := type of (fun (h : large_spec__stmt) => h RNG R K K2 Q FRESH ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n ctx t PA nres nsec lo sj sorted jstats jbsl jglob jslot) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (R, (K, (K2, (Q, (FRESH, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (n, (ctx, (t, (PA, (nres, (nsec, (lo, (sj, (sorted, (jstats, (jbsl, (jglob, jslot))))))))))))))))))))))))))))))))))))))))))))))))))))) as _.
 cbv zeta.
  intros ST CEIL LO MI TP -> -> -> -> N PRIM LC CX0 CX1 T0 T1 CT2 STATS LSJ INS SRT JST JBS MTX JGL
         PA0 PA1 PAL NSR NRM NRB0 JSL DPT DPC DPL RIMG RTLS RSTK RCTX RT RPA CXI TIC FROK UNR KONT1 SHAPE2 UNR3 UNR2 KONT2. band_lin.   (* [comment removed for export] *)
  pose proof PA0 as PA00. clear PA0. (nd_pre (ablk_int _ _ PA00) 6%nat; intros kP PA0 PA0a PA0b PA0c PA0d; nd_post).   (* [comment removed for export] *)
  (pose proof (sec_facts n N PRIM) as ndP__; nd_pre ndP__ 10%nat; intros NB RZ RSE RSR RSM NSE MSE MSR MSM MSB; nd_post).
  unfold AIMG_HI, AREQMAX, large_entry in *.
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - LARGE_STACK, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  chg (needed_size n) size. chg (sec_map_size n) ms.
  (* [comment removed for export] *)
  box STATS. box INS. box SRT. box JST. box JBS. box MTX. box JGL.
  (* [comment removed for export] *)
  assert (MS4 : exists q, ms = 4096 * q) by (exists (ms / 4096); clear -MSM MSB; Z.div_mod_to_equations; lia).
  clear RSE. box MSE. box RSM. box MSM. box NRM. box PAL. box CT2. box DPT. box DPC.
  (* [comment removed for export] *)
  iprefix.
  carve_frame 96%nat ST.
  do 12 step.                                                  (* [comment removed for export] *)
  assert (HWL : Forall (fun iv => (((snd iv <= AIMG_LO \/ AIMG_HI <= fst iv) /\ (snd iv <= ATPv + -88 \/ ATPv + -80 <= fst iv)) /\ (snd iv <= ctx + 152 \/ ctx + 160 <= fst iv)) \/ (0xab3f0 <= fst iv /\ snd iv <= 0xadc00))
                       [(bv_unsigned sp - LARGE_STACK, bv_unsigned sp)]%Z)
    by (apply Forall_cons; [cbn; left; unfold AIMG_HI, AIMG_LO; clear -SPR CEIL LO CX1 CXI; lia | apply Forall_nil]).
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (large_cells_frame ctx t PA m mm _ LC MU WM ltac:(exact CXI) HWL) as LC1 end.
  (nd_pre LC1 10%nat; intros RC PC GNM NAME TI TK T88 TSD CT I64; nd_post). unfold ATP88, ATSD in *.
  step. zstep. zstep. step. if_lit.                            (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  zstep. zstep. step. if_lit.                                  (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.                                  (* [comment removed for export] *)
  setreg 11 (Z_to_bv 64 (ms - 4096)) ltac:(rewrite land_align4096 by (clear -MSB MSR; lia); f_equal; unbox MSE; rewrite MSE; clear -MSB; Z.div_mod_to_equations; lia).
  zstep. zstep. zstep. zstep. zstep.                           (* [comment removed for export] *)
  change (Z.land ((0 - Z.b2z (4096 <? 8)) mod 18446744073709551616) 8) with 0.
  setreg 18 (Z_to_bv 64 ms) ltac:(f_equal; clear; lia).
  step. if_cases K0; zify_cond K0. 2: { exfalso. clear -K0 MSR MSB NSE RSR N. subst size. lia. }   (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  (* [comment removed for export] *)
  apply evtF_done.
  lazymatch goal with |- implS _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
  eapply (mmapz_spec RNG K Q FRESH _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mm ms lo) end.
  all: try lazymatch goal with
       | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -SPR CEIL LO; lia); exact ST
       | |- mem_inv _ _ => assumption
       | |- rmap_cells _ => exact RC
       | |- rng_aimg _ => exact RIMG
       | |- rng_atls _ => exact RTLS
       | |- @eq word _ _ => reflexivity
       | |- _ mod 4096 = 0 => unboxed MSM
       | |- bv_unsigned _ <> 0 => rewrite unsigned_lit by (clear; lia); clear; lia
       | |- rng _ _ (_ - _) => rewrite unsigned_lit by (clear -SPR CEIL LO; lia); eapply rng_sub'; [exact RSTK|]; clear -SPR CEIL LO; lia
       end.
  all: try (atop_facts; rewrite ?unsigned_lit by (clear -SPR CEIL LO; lia); clear -SPR CEIL LO MSB; lia).
  { (* [comment removed for export] *)
    intros a HFR A0 ACE. destruct (FROK a HFR) as (AH & _). unfold ablk, KLS, AIMG_HI in *.  (* [comment removed for export] *) rewrite unsigned_lit by (clear -SPR CEIL LO; lia). clear -AH ACE CEIL LO SPR. lia. }
  { (* [comment removed for export] *)
    intros a RNG' ms' HFR A0 AAL ACE LE. eapply UNR; eassumption. }
  (* [comment removed for export] *)
  intros a RNG' m2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HFR PO.
  (nd_pre PO 13%nat; intros FPLE BW AAL A0 ACE MU2 WM2 MI2 ST2 ZCH RCH RSCH RC2; nd_post).
  (nd_pre (FROK a HFR) 6%nat; intros AHI DAT DAC DAP SH0 DAL; nd_post). box DAT. box DAC. box DAP.
  pose proof AHI as AHI0. clear AHI. (nd_pre (ablk_int _ _ AHI0) 6%nat; intros kA AHI AHIa AHIb AHIc AHId; nd_post).   (* [comment removed for export] *)
  rewrite unsigned_lit in MU2, ST2 by (clear -SPR CEIL LO; lia).
  (* [comment removed for export] *)
  destruct (Z_lt_le_dec nsec 1048576) as [NSB|NSB].
  2: { eapply UNR3; [exact HFR | clear -NSB NSR NRB0; lia | clear -NSB NSR NRB0; lia]. }
  (* [comment removed for export] *)
  set (CW := if nsec =? nres then 131072 else 0).
  assert (ECW : CW = (if nsec =? nres then 131072 else 0)) by reflexivity.
  assert (CWF : 0 <= CW <= 131072 /\ 8 * nres + CW <= 8388608).
  { rewrite ECW. ub NRM. destruct (Z.eqb_spec nsec nres) as [E|E]; clear -NSB NSR NRB0 Y E; Z.div_mod_to_equations; lia. }
  clearbody CW. box ECW.
  atop_facts.
  assert (SZ8 : size mod 8 = 0) by (rewrite NSE; ub RSM; clear -Y; Z.div_mod_to_equations; lia).
  assert (SZP : 0 < size) by (rewrite NSE; clear -RSR N; lia).
  assert (SHR : 0x800b8800 <= shad a /\ shad a + ms / 8 <= 0x10007fff8000 /\ shlen ms = ms / 8 /\ shlen 4096 = 512
                /\ shad (a + 4096 + size) = shad a + 512 + size / 8 /\ shlen (ms - 4096 - size) = ms / 8 - 512 - size / 8).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by (clear; lia). change (2^3) with 8. ub MSM. clear -AHI AHIa AHIb AHIc AHId ACE MSB AAL SZ8 K0 Y. Z.div_mod_to_equations. lia. }
  (nd_pre SHR 6%nat; intros SH1 SH2 SH3 SH4 SH5 SH6; nd_post). rewrite SH3 in RSCH.
  (nd_pre (ablk_shad_int _ _ AHI0 ltac:(clear -AAL; Z.div_mod_to_equations; lia) ltac:(clear -MSB; lia)) 6%nat; intros kS ASD ASDa ASDb _ _; nd_post).   (* [comment removed for export] *)
  (nd_pre (sclr_int _ _ T0 ltac:(clear -TIC; lia) ltac:(clear -T1; lia)) 4%nat; intros kT TBND TBNDa TBNDb; nd_post). (nd_pre (sclr_int _ _ CX0 ltac:(clear -CXI; lia) ltac:(clear -CX1; lia)) 4%nat; intros kC CBND CBNDa CBNDb; nd_post).   (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (MU02 : munch [(bv_unsigned sp - LARGE_STACK, bv_unsigned sp + -96); (a, a + ms)]%Z m0 m2)
    by (eapply munch_weaken; [| exact MU2]; unfold sub_fp; cbn [outside]; clear; intros q Hq; lia).
  assert (MUA : munch [(bv_unsigned sp - LARGE_STACK, bv_unsigned sp); (a, a + ms)]%Z m m2).
  { eapply munch_trans; [eapply munch_weaken; [| exact MU] | eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside]; clear; intros q Hq; lia. }
  assert (WMA : wmono asegs m m2) by (eapply wmono_trans; [exact WM | exact WM2]).
  clear MU WM MU2.
  xport FR MU02 WM2 ltac:(clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE; dlia).
  xport I64 MU02 WM2 ltac:(clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE; dlia).
  xport GNM MU02 WM2 ltac:(clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE; dlia). xport NAME MU02 WM2 ltac:(clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE; dlia).
  xport TI MU02 WM2 ltac:(clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE; dlia). xport TK MU02 WM2 ltac:(clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE; dlia).
  xport T88 MU02 WM2 ltac:((nd_pre (tclr_int_lem _ _ DAL ltac:(clear -AHIa; lia) ltac:(clear -AHId; atop_facts; lia)) 4%nat; intros kL DALk DALa DALb; nd_post); clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE DALk DALa DALb; dlia).      (* [comment removed for export] *) xport TSD MU02 WM2 ltac:(clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE; dlia).
  xport CT MU02 WM2 ltac:(ub DAC; clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE CX0 CX1 Y CXI; dlia).
  assert (PC2 : poison_cells m2).
  { eapply poison_cells_frame; [exact PC | exact MU02 | exact WM2 |]. unfold AIMG_HI.
    apply Forall_cons; [cbn; clear -SPR CEIL LO; lia|]. apply Forall_cons; [cbn; clear -AHI AHIa AHIb AHIc AHId; lia| apply Forall_nil]. }
  clear PC RC ST.
  unfold fill_at in SH0. xport SH0 MUA WMA ltac:(clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE SH1 SH2 MSB; dlia).
  unbox STATS. xport STATS MUA WMA ltac:(ub DAT; rewrite LSJ; clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE T0 T1 Y TIC; dlia).
  unbox INS. xport INS MUA WMA ltac:(clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE; dlia).
  unbox SRT. xport SRT MUA WMA ltac:(clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE; dlia).
  unbox JST. xport JST MUA WMA ltac:(clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE; dlia).
  unbox JBS. xport JBS MUA WMA ltac:(clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE; dlia).
  unbox MTX. xport MTX MUA WMA ltac:(clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE; dlia).
  unbox JGL. xport JGL MUA WMA ltac:(clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE; dlia).
  assert (JSL2 : nsec < nres -> rw_cells asegs m2 (PA + 8 * nsec) [CB 8 jslot]).
  { intros LT. specialize (JSL LT). xport JSL MUA WMA ltac:(ub DAP; clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF LT Y; dlia). exact JSL. }
  clear JSL.
  (* [comment removed for export] *)
  change (rw_cells asegs m2 (shad a) [CB (Z.to_nat (ms / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (ms / 8)))]) with (fill_at m2 (shad a) (ms / 8) 0) in SH0.
  destruct (fill_split m2 (shad a) 512 (ms / 8 - 512) 0 ltac:(replace (512 + (ms / 8 - 512)) with (ms / 8) by (clear; lia); exact SH0) ltac:(clear; lia) ltac:(clear -MSB; Z.div_mod_to_equations; lia))
    as [SHH SHR0].
  destruct (fill_split m2 (shad a + 512) (size / 8) (ms / 8 - 512 - size / 8) 0 ltac:(replace (size / 8 + (ms / 8 - 512 - size / 8)) with (ms / 8 - 512) by (clear; lia); exact SHR0)
              ltac:(clear -SZP; Z.div_mod_to_equations; lia) ltac:(ub MSM; clear -MSB K0 SZ8 Y MSR; Z.div_mod_to_equations; lia))
    as [SHU SHT]. clear SHR0.
  clear SH0.
  (* [comment removed for export] *)
  apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RTLS. apply (rng_fp_le _ _ _ _ FPLE) in RSTK. apply (rng_fp_le _ _ _ _ FPLE) in RCTX.
  apply (rng_fp_le _ _ _ _ FPLE) in RT. apply (rng_fp_le _ _ _ _ FPLE) in RPA.
  iprefix.
  replace (ret_pc (Z_to_bv 64 231300)) with (Z_to_bv 64 231300 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
  step. if_cases K1; zify_cond K1. { exfalso. clear -K1 A0 ACE. lia. }          (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  zstep. zstep.                                                (* [comment removed for export] *)
  setreg 11 (Z_to_bv 64 0) ltac:(f_equal; rewrite (Z.land_comm 4095 a); change 4095 with (Z.ones 12); rewrite Z.land_ones by (clear -A0; lia); change (2^12) with 4096; symmetry; exact AAL).
  step. if_lit.                                                (* [comment removed for export] *)
  zstep. zstep. zstep.                                         (* [comment removed for export] *)
  setreg 11 (Z_to_bv 64 0) ltac:(f_equal; change 7 with (Z.ones 3); rewrite Z.land_ones by (clear -A0; lia); change (2^3) with 8; clear -AAL A0; Z.div_mod_to_equations; lia).
  zstep. zstep. zstep. zstep. zstep.                           (* [comment removed for export] *)
  change ((Z.b2z (0 <? 1) + -1) mod 18446744073709551616) with 0. change (Z.land 0 8) with 0.
  setreg 25 (Z_to_bv 64 (a + 4096)) ltac:(f_equal; clear; lia).
  zstep. zstep. zstep. zstep.                                  (* [comment removed for export] *)
  setreg 23 (Z_to_bv 64 (a + 4096 + size))
    ltac:(f_equal; change 18446744073709551608 with (2^64 - 2^3); rewrite land_align_down by (clear -A0 ACE K0 SZP; lia);
          change (2^3) with 8; clear -AAL SZ8 A0; Z.div_mod_to_equations; lia).
  setreg 10 (Z_to_bv 64 (a + 4096))
    ltac:(f_equal; change 18446744073709551608 with (2^64 - 2^3); rewrite land_align_down by (clear -A0 ACE K0 MSB; lia);
          change (2^3) with 8; clear -AAL A0; Z.div_mod_to_equations; lia).
  zstep. step. step.                                           (* [comment removed for export] *)
  setreg 11 (Z_to_bv 64 4096) ltac:(f_equal; clear; lia).
  (* [comment removed for export] *)
  clear MU02.
  apply (munch_weaken _ [(bv_unsigned sp - LARGE_STACK, bv_unsigned sp); (a, a + ms); (shad a, shad a + ms / 8);
                          (0xab408, 0xab668); (t + 2800, t + 3168);
                          (PA + 8 * nsec, PA + 8 * nsec + 8); (PA + 8 * nres, PA + 8 * nres + CW)]%Z) in MUA.
  2: { unfold sub_fp. cbn [outside]. clear. intros q Hq. tauto. }
  (* [comment removed for export] *)
  unfold fill_at in SHH, SHU, SHT.
  pose proof PC2 as PCx. (nd_pre PCx 7%nat; intros P1 P2 P3 P4 P5 P6 P7; nd_post).
  pose proof RC2 as RCx. (nd_pre RCx 5%nat; intros Q1 Q2 Q3 Q4 Q5; nd_post). clear PC2 RC2 Q3.
  Local Ltac pcells := unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end); assumption.
  (* [comment removed for export] *)
  assert (RSH1 : rng RNG' (shad a) 512) by (eapply rng_sub'; [exact RSCH|]; clear -MSB; Z.div_mod_to_equations; lia).
  pose proof (munch_refl [(bv_unsigned sp + -96 - 64, bv_unsigned sp + -96); (shad a, shad a + 512)]%Z m2) as MUS. pose proof (wmono_refl asegs m2) as WMS.
  match goal with H : stk asegs ?mm _ _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into STK__; box STK__ end. box SHH.   (* [comment removed for export] *)
  step. call_sp (poison_shadow_spec_k RNG' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a 4096 512 250 lo).   (* [comment removed for export] *)
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => try clear STK__; try clear SHH
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- stk _ _ _ _ => unboxed STK__
       | |- mem_inv _ _ => assumption
       | |- poison_cells _ => pcells
       | |- @eq word _ _ => reflexivity
       | |- rw_cells _ _ (shad _) _ => unboxed SHH
       | |- rng _ (shad _) _ => exact RSH1
       | |- rng_aimg _ => exact RIMG
       | |- rng_atls _ => exact RTLS
       | |- shlen _ = _ => exact SH4
       | |- rng _ _ _ => solve_rng
       end.
  all: try (eapply ablk_sub; [exact AHI0 | clear; lia | clear -MSB; lia]).
  all: try (atop_facts; clear -AAL A0 AHI AHIa AHIb AHIc AHId ACE MSB SPR CEIL LO; first [lia | Z.div_mod_to_equations; lia]).
  lazymatch goal with M : munch _ m2 ?mm, W : wmono asegs m2 _ |- _ =>
    assert (JSL3 : nsec < nres -> rw_cells asegs mm (PA + 8 * nsec) [CB 8 jslot])
      by (intros LT; specialize (JSL2 LT); xport JSL2 M W ltac:(clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF LT SH1 SH2 MSB; dlia); exact JSL2);
    clear JSL2 M W; rename JSL3 into JSL2 end.
  (* [comment removed for export] *)
  zstep. step. step.                                           (* [comment removed for export] *)
  setreg 11 (Z_to_bv 64 (ms - 4096 - size)) ltac:(f_equal; clear; lia).
  assert (RSH2 : rng RNG' (shad (a + 4096 + size)) (ms / 8 - 512 - size / 8))
    by (rewrite SH5; eapply rng_sub'; [exact RSCH|]; ub MSM; clear -MSB MSR SZP SZ8 K0 Y; Z.div_mod_to_equations; lia).
  rewrite <- SH5 in SHT.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (munch_refl [(bv_unsigned sp + -96 - 64, bv_unsigned sp + -96); (shad (a + 4096 + size), shad (a + 4096 + size) + (ms / 8 - 512 - size / 8))]%Z mm) as MUS;
    pose proof (wmono_refl asegs mm) as WMS end.
  match goal with H : stk asegs ?mm _ _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into STK__; box STK__ end. box SHT.   (* [comment removed for export] *)
  step. call_sp (poison_shadow_spec0_k RNG' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (a + 4096 + size) (ms - 4096 - size) (ms / 8 - 512 - size / 8) 250 lo).   (* [comment removed for export] *)
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => try clear STK__; try clear SHT
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- stk _ _ _ _ => unboxed STK__
       | |- mem_inv _ _ => assumption
       | |- poison_cells _ => pcells
       | |- @eq word _ _ => reflexivity
       | |- rw_cells _ _ (shad _) _ => unboxed SHT
       | |- rng _ (shad _) _ => exact RSH2
       | |- rng_aimg _ => exact RIMG
       | |- rng_atls _ => exact RTLS
       | |- shlen _ = _ => exact SH6
       | |- rng _ _ _ => solve_rng
       end.
  all: try (eapply ablk_sub; [exact AHI0 | clear -SZP; lia | clear; lia]).   (* [comment removed for export] *)
  all: try (atop_facts; ub MSM; clear -AAL A0 AHI AHIa AHIb AHIc AHId ACE MSB MSR SPR CEIL LO SZ8 SZP K0 Y; first [lia | Z.div_mod_to_equations; lia]).
  lazymatch goal with M : munch _ ?mo ?mm, W : wmono asegs ?mo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (JSL3 : nsec < nres -> rw_cells asegs mm (PA + 8 * nsec) [CB 8 jslot])
      by (intros LT; specialize (JSL2 LT); xport JSL2 M W ltac:(ub MSM; clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF LT SH1 SH2 SH5 MSB MSR SZP SZ8 K0 Y; Z.div_mod_to_equations; dlia); exact JSL2);
    clear JSL2 M W; rename JSL3 into JSL2 end.
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (munch_refl [(bv_unsigned sp + -96 - 32, bv_unsigned sp + -96)]%Z mm) as MUS; pose proof (wmono_refl asegs mm) as WMS end.
  pose proof CT as CT0. box CT0. box ZCH. box POST. box POST0. box SHU.   (* [comment removed for export] *)
  match goal with H : stk asegs ?mm _ _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into STK__; box STK__ end.   (* [comment removed for export] *)
  step. call_sp (thread_stats_spec RNG' ctx t lo).   (* [comment removed for export] *)
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => try clear STK__
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- stk _ _ _ _ => unboxed STK__
       | |- mem_inv _ _ => assumption
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- rw_cells _ _ _ _ => assumption
       | |- rng_aimg _ => exact RIMG
       | |- rng_atls _ => exact RTLS
       | |- rng _ _ _ => solve_rng
       end.
  all: try (unfold AIMG_HI; clear -CEIL LO CX0 CX1 T0 T1 SPR CXI TIC; lia).
  lazymatch goal with M : munch _ ?mo ?mm, W : wmono asegs ?mo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (JSL3 : nsec < nres -> rw_cells asegs mm (PA + 8 * nsec) [CB 8 jslot])
      by (intros LT; specialize (JSL2 LT); xport JSL2 M W ltac:(clear -SPR CEIL LO PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF LT; dlia); exact JSL2);
    clear JSL2; rename JSL3 into JSL2;
    (* [comment removed for export] *)
    apply (munch_weaken _ [(bv_unsigned sp + -96 - 32, bv_unsigned sp + -96); (t + 2872, t + 2888)]%Z) in M;
    [ rename M into MUS2; rename W into WMS2 | unfold sub_fp; cbn [outside]; clear; intros q Hq; tauto ] end.
  clear CT.
  (* [comment removed for export] *)
  snapshot [(t + 2872, t + 2888); (a, a + 32); (0xab640, 0xab644)]%Z MUz WMz.
  aload STATS 9 (t + 2800 + 72).                               (* [comment removed for export] *)
  aload STATS 10 (t + 2800 + 80).                              (* [comment removed for export] *)
  zstep.                                                       (* [comment removed for export] *)
  setreg 14 (Z_to_bv 64 0) ltac:(f_equal; change 7 with (Z.ones 3); rewrite Z.land_ones by (clear -A0; lia); change (2^3) with 8; clear -AAL A0; Z.div_mod_to_equations; lia).
  zstep. zstep.                                                (* [comment removed for export] *)
  astore STATS 9.                                              (* [comment removed for export] *)
  astore STATS 10.                                             (* [comment removed for export] *)
  carry ZCH MUS2 WMS2 ltac:(ub DAT; clear -Y SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB T1 TIC; dlia).
  carry POST MUS2 WMS2 ltac:(clear -SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB SH1 SH2 SH4 T1 TBND TBNDa TBNDb; dlia).   (* [comment removed for export] *)
  carry SHU MUS2 WMS2 ltac:(clear -SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB MSR SH1 SH2 SH4 SZP K0 T1 TBND TBNDa TBNDb; Z.div_mod_to_equations; dlia).
  carry POST0 MUS2 WMS2 ltac:(rewrite SH5; ub MSM; clear -Y SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB MSR SH1 SH2 SH4 SZP SZ8 K0 T1 TBND TBNDa TBNDb; Z.div_mod_to_equations; dlia).
  clear MUS2 WMS2.
  step. if_lit.                                                (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  zstep. zstep.                                                (* [comment removed for export] *)
  setreg 12 (Z_to_bv 64 0) ltac:(f_equal; try rewrite (Z.land_comm 4095); change 4095 with (Z.ones 12); rewrite Z.land_ones by (clear -A0; lia); change (2^12) with 4096; clear -AAL A0; Z.div_mod_to_equations; lia).
  step. if_lit.                                                (* [comment removed for export] *)
  step. if_cases K5; zify_cond K5. { exfalso. clear -K5 A0 SZP ACE MSR. lia. }       (* [comment removed for export] *)
  step. if_cases K6; zify_cond K6. { exfalso. clear -K6 A0 SZP ACE MSR. lia. }       (* [comment removed for export] *)
  zstep.                                                       (* [comment removed for export] *)
  setreg 21 (Z_to_bv 64 a) ltac:(f_equal; clear; lia).
  (* [comment removed for export] *)
  lazymatch type of ZCH with rw_cells _ ?mq _ _ =>
    change (fill_at mq a ms 0) in ZCH;
    destruct (fill_split mq a 32 (ms - 32) 0 ltac:(replace (32 + (ms - 32)) with ms by (clear; lia); exact ZCH) ltac:(clear; lia) ltac:(clear -MSB; lia)) as [ZH ZR];
    destruct (fill_split mq (a + 32) (4096 - 32) (ms - 4096) 0 ltac:(replace (4096 - 32 + (ms - 4096)) with (ms - 32) by (clear; lia); exact ZR) ltac:(clear; lia) ltac:(clear -MSB; lia)) as [ZP ZU]
  end.
  clear ZCH ZR. apply zeros32_hdr in ZH. unfold fill_at in ZP, ZU. replace (a + 32 + (4096 - 32)) with (a + 4096) in ZU by (clear; lia).
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (JSL3 : nsec < nres -> rw_cells asegs mm (PA + 8 * nsec) [CB 8 jslot])
      by (intros LT; specialize (JSL2 LT); xport JSL2 MUz WMz ltac:(ub DPT; ub DAP; clear -Y Y0 SPR CEIL LO PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF LT T1 AHI AHIa AHIb AHIc AHId ACE MSB TIC; dlia); exact JSL2);
    clear JSL2 MUz WMz; rename JSL3 into JSL2 end.
  box STATS. box ZP. box ZU. box POST. box POST0. box SHU.   (* [comment removed for export] *)
  snapshot [(bv_unsigned sp - LARGE_STACK, bv_unsigned sp); (a, a + 32); (0xab408, 0xab668);
            (PA + 8 * nsec, PA + 8 * nsec + 8); (PA + 8 * nres, PA + 8 * nres + CW)]%Z MUr WMr.
  snapshot [(a, a + 32); (0xab640, 0xab644)]%Z MUq WMq.      (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  step. if_cases K7; zify_cond K7. { exfalso. clear -K7 MSB. lia. }                 (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep. step. zstep. step.                                    (* [comment removed for export] *)
  apply (mtx_to_C4 _ 0 ltac:(clear; lia)) in MTX.
  assert (AMO : amo_aligned AW (Z_to_bv 64 702016) = true) by (apply amo_alignedW_intro; [clear; lia| reflexivity]).
  amo_stepA AMO.                                               (* [comment removed for export] *)
  step. zstep. zstep. zstep.                                   (* [comment removed for export] *)
  amo_stepA AMO.                                               (* [comment removed for export] *)
  step. if_lit.                                                (* [comment removed for export] *)
  zstep. step. if_lit.                                         (* [comment removed for export] *)
  (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  zstep.                                                       (* [comment removed for export] *)
  setreg 11 (Z_to_bv 64 0) ltac:(f_equal; rewrite Z.shiftr_div_pow2 by (clear; lia); clear -NSR NSB; Z.div_mod_to_equations; lia).
  step. if_lit.                                                (* [comment removed for export] *)
  (* [comment removed for export] *)
  pose proof (slog_facts ms MSB ltac:(ub MSM; exact Y)) as [CSR CLZ].
  (* [comment removed for export] *)
  do 5 zstep.                                                  (* [comment removed for export] *)
  remember (Z.lor ms (Z.shiftr ms 1)) as y1 eqn:Ey1. assert (Ry1 : (0 <= y1 < 2^64)%Z) by (change (inr64 y1); rewrite Ey1; zrange).
  do 5 zstep.                                                  (* [comment removed for export] *)
  remember (Z.lor y1 (Z.shiftr y1 2)) as y2 eqn:Ey2. assert (Ry2 : (0 <= y2 < 2^64)%Z) by (change (inr64 y2); rewrite Ey2; zrange).
  do 8 zstep.                                                  (* [comment removed for export] *)
  remember (Z.lor y2 (Z.shiftr y2 4)) as y3 eqn:Ey3. assert (Ry3 : (0 <= y3 < 2^64)%Z) by (change (inr64 y3); rewrite Ey3; zrange).
  do 2 zstep. remember (Z.lor y3 (Z.shiftr y3 8)) as y4 eqn:Ey4. assert (Ry4 : (0 <= y4 < 2^64)%Z) by (change (inr64 y4); rewrite Ey4; zrange).
  do 2 zstep. remember (Z.lor y4 (Z.shiftr y4 16)) as y5 eqn:Ey5. assert (Ry5 : (0 <= y5 < 2^64)%Z) by (change (inr64 y5); rewrite Ey5; zrange).
  do 2 zstep. remember (Z.lor y5 (Z.shiftr y5 32)) as y6 eqn:Ey6. assert (Ry6 : (0 <= y6 < 2^64)%Z) by (change (inr64 y6); rewrite Ey6; zrange).
  zstep.                                                       (* [comment removed for export] *)
  setreg 11 (Z_to_bv 64 (cb_sm ms)) ltac:(subst y6 y5 y4 y3 y2 y1; reflexivity).              (* [comment removed for export] *)
  zstep. clear Ry6 Ey6 y6 Ry5 Ey5 y5 Ry4 Ey4 y4 Ry3 Ey3 y3 Ry2 Ey2 y2 Ry1 Ey1 y1.   (* [comment removed for export] *)
  do 6 zstep. step. do 9 zstep.                                (* [comment removed for export] *)
  setreg 19 (Z_to_bv 64 (cb_clz (cb_sm ms))) ltac:(reflexivity).
  step. if_cases KQ; zify_cond KQ.
  - (* [comment removed for export] *)
    clear MUq WMq JSL2. subst nsec.
    assert (NRB : nres + 16384 <= 1048576) by (ub NRM; clear -NSB Y NSR; Z.div_mod_to_equations; lia).
    assert (ECW1 : CW = 131072) by (ub ECW; rewrite Z.eqb_refl in Y; exact Y).
    clear CWF. assert (CWF : CW = 131072 /\ nres + 16384 <= 1048576) by (split; [exact ECW1| exact NRB]).
    step.                                                      (* [comment removed for export] *)
    zstep. zstep. zstep.                                       (* [comment removed for export] *)
    setreg 11 (Z_to_bv 64 (PA + 8 * nres)) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by (clear; lia); clear -NSR; lia).
    step. step. step. step.                                    (* [comment removed for export] *)
    step.                                                      (* [comment removed for export] *)
    apply evtF_done. rewrite (SHAPE2 a HFR eq_refl NRB).
    lazymatch goal with |- implS _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (rmapd_spec RNG' (K2 a) Q _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mm (PA + 8 * nres) 131072 lo) end.
    all: try lazymatch goal with
         | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -SPR CEIL LO; lia); eassumption
         | |- mem_inv _ _ => assumption
         | |- rmap_cells _ => unfold rmap_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end); assumption
         | |- rng_aimg _ => exact RIMG
         | |- rng_atls _ => exact RTLS
         | |- @eq word _ _ => reflexivity
         | |- rng _ _ (_ - _) => rewrite unsigned_lit by (clear -SPR CEIL LO; lia); eapply rng_sub'; [exact RSTK|]; clear -SPR CEIL LO; lia
         | |- (_ + 8 * _) mod 4096 = 0 => ub NRM; ub PAL; clear -Y Y0 NSR; Z.div_mod_to_equations; lia
         end.
    all: try (unfold AIMG_HI; rewrite ?unsigned_lit by (clear -SPR CEIL LO; lia); clear -SPR CEIL LO PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF; lia).
    { (* [comment removed for export] *) intros r RNG'' ms' NE R0 RCE. eapply UNR2; [exact NE | exact R0 | exact RCE]. }
    (* [comment removed for export] *)
    intros RNG'' mc q0 q1 q2 b1 b2 b3 b4 b5 b6 b7 q3 q4 q5 q6 PM.
    (nd_pre PM 11%nat; intros FPLE2 PCE MUc WMc MIc STc ZC RPC RSPC BW2 RCc; nd_post).
    rewrite unsigned_lit in MUc, STc by (clear -SPR CEIL LO; lia).
    (* [comment removed for export] *)
    xport FR MUc WMc ltac:(clear -SPR CEIL LO PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF AHI AHIa AHIb AHIc AHId ACE MSB SH1 SH2; dlia).
    xport I64 MUc WMc ltac:(clear -SPR CEIL LO PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF AHI AHIa AHIb AHIc AHId ACE MSB SH1 SH2; dlia).
    xport INS MUc WMc ltac:(clear -SPR CEIL LO PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF AHI AHIa AHIb AHIc AHId ACE MSB SH1 SH2; dlia).
    xport SRT MUc WMc ltac:(clear -SPR CEIL LO PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF AHI AHIa AHIb AHIc AHId ACE MSB SH1 SH2; dlia).
    xport JST MUc WMc ltac:(clear -SPR CEIL LO PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF AHI AHIa AHIb AHIc AHId ACE MSB SH1 SH2; dlia).
    xport JBS MUc WMc ltac:(clear -SPR CEIL LO PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF AHI AHIa AHIb AHIc AHId ACE MSB SH1 SH2; dlia).
    xport MTX MUc WMc ltac:(clear -SPR CEIL LO PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF AHI AHIa AHIb AHIc AHId ACE MSB SH1 SH2; dlia).
    xport JGL MUc WMc ltac:(clear -SPR CEIL LO PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF AHI AHIa AHIb AHIc AHId ACE MSB SH1 SH2; dlia).
    (* [comment removed for export] *)
    xport ZH MUc WMc ltac:(ub DAP; clear -Y SPR CEIL LO PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF AHI AHIa AHIb AHIc AHId ACE MSB; dlia).
    lazymatch type of MUr with munch ?Wr ?ma ?mb =>
      assert (MUr2 : munch Wr ma mc) by (eapply munch_trans; [exact MUr | eapply munch_weaken; [| exact MUc]; unfold sub_fp; cbn [outside]; clear -CWF; intros q Hq; lia]);
      assert (WMr2 : wmono asegs ma mc) by (eapply wmono_trans; [exact WMr | exact WMc]) end.
    clear MUr WMr. rename MUr2 into MUr. rename WMr2 into WMr.
    lazymatch type of MUA with munch ?Wa ?ma ?mb =>
      assert (MUA2 : munch Wa ma mc) by (eapply munch_trans; [exact MUA | eapply munch_weaken; [| exact MUc]; unfold sub_fp; cbn [outside]; clear -CWF; intros q Hq; lia]);
      assert (WMA2 : wmono asegs ma mc) by (eapply wmono_trans; [exact WMA | exact WMc]) end.
    clear MUA WMA MUc WMc. rename MUA2 into MUA. rename WMA2 into WMA.
    apply (rng_fp_le _ _ _ _ FPLE2) in RIMG. apply (rng_fp_le _ _ _ _ FPLE2) in RTLS. apply (rng_fp_le _ _ _ _ FPLE2) in RSTK. apply (rng_fp_le _ _ _ _ FPLE2) in RCH.
    apply (rng_fp_le _ _ _ _ FPLE2) in RSCH. apply (rng_fp_le _ _ _ _ FPLE2) in RPA.
    iprefix.
    replace (ret_pc (Z_to_bv 64 232228)) with (Z_to_bv 64 232228 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
    step.                                                      (* [comment removed for export] *)
    step. step.                                                (* [comment removed for export] *)
    step. zstep.                                               (* [comment removed for export] *)
    step.                                                      (* [comment removed for export] *)
    step.                                                      (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch type of ZC with rw_cells _ ?mq _ _ =>
      change (fill_at mq (PA + 8 * nres) 131072 0) in ZC;
      destruct (fill_split mq (PA + 8 * nres) 8 (131072 - 8) 0 ZC ltac:(clear; lia) ltac:(clear; lia)) as [ZC8 ZCR] end.
    clear ZC. unfold fill_at in ZC8, ZCR.
    assert (RPS : rng RNG'' (PA + 8 * nres) 8) by (eapply rng_sub'; [exact RPC|]; clear; lia).
    eapply evtF_cut.
    { eapply (large_tail_spec RNG'' (bv_unsigned sp)); try easm.
      all: try reflexivity.
      all: try (ub DAP; atop_facts; clear -Y CEIL LO SPR NSR NRB0 CWF PCE; lia). }
    cbv beta. intros ms9 PT. unfold large_tail_post in PT.
    (nd_pre PT 16%nat; intros u0 u1 u2 c1 c2 c3 c4 c5 c6 c7 u3 u4 u5 u6 m9 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 12%nat; intros MU9 WM9 MI9 ST9 ZH9 INS9 SRT9 JST9 JBS9 MTX9 JGL9 PAS9; nd_post).
    apply evtF_done. rewrite Z_to_bv_bv_unsigned.
    lazymatch type of MUr with munch ?Wr ?ma ?mb =>
      assert (MUr9 : munch Wr ma m9) by (eapply munch_trans; [exact MUr | eapply munch_weaken; [| exact MU9]; unfold sub_fp; cbn [outside]; clear -CWF; intros q Hq; lia]);
      assert (WMr9 : wmono asegs ma m9) by (eapply wmono_trans; [exact WMr | exact WM9]) end.
    clear MUr WMr. rename MUr9 into MUr. rename WMr9 into WMr.
    carry ZP MUr WMr ltac:(ub DAP; clear -Y SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB NSR NRB0 CWF; dlia).
    carry ZU MUr WMr ltac:(ub DAP; clear -Y SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB NSR NRB0 CWF; dlia).
    carry STATS MUr WMr ltac:(ub DAT; ub DPT; rewrite ?upd_length, ?LSJ; clear -Y Y0 SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB NSR NRB0 CWF T0 T1 PA0 PA0a PA0b PA0c PA0d PA1 TIC; dlia).
    carry POST MUr WMr ltac:(clear -SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB SH1 SH2 SH4 NSR NRB0 CWF PA0 PA0a PA0b PA0c PA0d ASD ASDa ASDb; dlia).   (* [comment removed for export] *)
    carry SHU MUr WMr ltac:(clear -SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB MSR SH1 SH2 SH4 NSR NRB0 CWF PA0 PA0a PA0b PA0c PA0d SZP K0 ASD ASDa ASDb; Z.div_mod_to_equations; dlia).
    carry POST0 MUr WMr ltac:(rewrite SH5; ub MSM; clear -Y SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB MSR SH1 SH2 SH4 NSR NRB0 CWF PA0 PA0a PA0b PA0c PA0d SZP SZ8 K0 ASD ASDa ASDb; Z.div_mod_to_equations; dlia).
    xport ZCR MU9 WM9 ltac:(ub DAP; clear -Y SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB NSR NRB0 CWF PA0 PA0a PA0b PA0c PA0d PA1; dlia).
    assert (MUF : munch [(bv_unsigned sp - LARGE_STACK, bv_unsigned sp); (a, a + ms); (shad a, shad a + ms / 8);
                         (0xab408, 0xab668); (t + 2800, t + 3168);
                         (PA + 8 * nres, PA + 8 * nres + 8); (PA + 8 * nres, PA + 8 * nres + CW)]%Z m m9).
    { eapply munch_trans; [exact MUA|]. eapply munch_weaken; [| exact MU9]. unfold sub_fp. cbn [outside]. clear -MSB CWF. intros q Hq. lia. }
    assert (WMF : wmono asegs m m9) by (eapply wmono_trans; [exact WMA | exact WM9]).
    eapply (KONT2 a RNG'' m9); [exact HFR | reflexivity |].
    unfold large_post. cbv zeta. change (needed_size n) with size. change (sec_map_size n) with ms.
    split; [eapply fp_le_trans; [exact FPLE| exact FPLE2]|]. split; [exact BW2|]. split; [exact AAL|]. split; [exact AHI0|]. split; [atop_facts; exact ACE|].
    split; [eapply munch_weaken; [| exact MUF]; unfold sub_fp, AINSTANCE; cbn [outside]; clear -CWF; intros q Hq; lia|]. split; [exact WMF|]. split; [exact MI9|]. split; [exact ST9|].
    split. { apply (proj2 (rw_cells_app asegs m9 a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 size); C8 (Z_to_bv 64 nres)] [CB _ _])).
             split; [exact ZH9|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. exact ZP. }
    split; [exact ZU|].
    split; [exact POST|]. split; [exact SHU|]. split; [unfold fill_at; rewrite <- SH5; exact POST0|].
    split; [exact RCH|]. split; [exact RSCH|].
    split; [exact INS9|]. split; [exact SRT9|]. split; [exact JST9|]. split; [exact JBS9|]. split; [exact MTX9|]. split; [exact JGL9|].
    split; [eexists; split; [exact STATS| rewrite !upd_length; exact LSJ]|].
    split; [exact PAS9|].
    split; [right; split; [reflexivity|]; split; [reflexivity|]; split; [exact ZCR| exact RPC]|].
    split; [clear -CWF; lia|].
    eapply (large_cells_frame ctx t PA m m9); [exact LC | exact MUF | exact WMF | exact CXI |].
    (nd_pre (tclr_int_lem _ _ DAL ltac:(clear -AHIa; lia) ltac:(clear -AHId; atop_facts; lia)) 4%nat; intros kL DALk DALa DALb; nd_post). (nd_pre (tclr_int_lem _ _ DPL ltac:(clear -PA0a; lia) ltac:(clear -PA0d; atop_facts; lia)) 4%nat; intros kPL DPLk DPLa DPLb; nd_post).      (* [comment removed for export] *)
    ub DAC. ub DPC. ub CT2. unfold AIMG_HI, AIMG_LO. clear -DALk DALa DALb DPLk DPLa DPLb Y Y0 Y1 SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE CX0 CX1 PA0 PA0a PA0b PA0c PA0d PA1 SH1 SH2 MSB T0 T1 NSR NRB0 CWF CXI TIC CBND CBNDa CBNDb TBND TBNDa TBNDb.   (* [comment removed for export] *)
    repeat (apply Forall_cons; [cbn [fst snd]; first [right; lia | left; lia] |]). apply Forall_nil.
  - (* [comment removed for export] *)
    assert (ECW0 : CW = 0) by (ub ECW; destruct (Z.eqb_spec nsec nres) as [E|E]; [exfalso; exact (KQ E) | exact Y]).
    clear CWF. assert (CWF : CW = 0 /\ nres <= 1048576) by (split; [exact ECW0| exact NRB0]).
    specialize (JSL2 ltac:(clear -KQ NSR; lia)).
    xport JSL2 MUq WMq ltac:(ub DAP; clear -Y SPR CEIL LO NSR NRB0 CWF PA0 PA0a PA0b PA0c PA0d PA1 AHI AHIa AHIb AHIc AHId ACE MSB KQ; dlia). clear MUq WMq.
    assert (RPS : rng RNG' (PA + 8 * nsec) 8) by (eapply rng_sub'; [exact RPA|]; clear -KQ NSR; lia).
    eapply evtF_cut.
    { eapply (large_tail_spec RNG' (bv_unsigned sp)); try easm.
      all: try reflexivity.
      all: try (ub DAP; clear -Y CEIL LO SPR NSR NRB0 CWF KQ; lia). }
    cbv beta. intros ms9 PT. unfold large_tail_post in PT.
    (nd_pre PT 16%nat; intros u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m9 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 12%nat; intros MU9 WM9 MI9 ST9 ZH9 INS9 SRT9 JST9 JBS9 MTX9 JGL9 PAS9; nd_post).
    apply evtF_done. rewrite Z_to_bv_bv_unsigned.
    (* [comment removed for export] *)
    lazymatch type of MUr with munch ?Wr ?ma ?mb =>
      assert (MUr9 : munch Wr ma m9) by (eapply munch_trans; [exact MUr | eapply munch_weaken; [| exact MU9]; unfold sub_fp; cbn [outside]; clear -CWF; intros q Hq; lia]);
      assert (WMr9 : wmono asegs ma m9) by (eapply wmono_trans; [exact WMr | exact WM9]) end.
    clear MUr WMr. rename MUr9 into MUr. rename WMr9 into WMr.
    carry ZP MUr WMr ltac:(ub DAP; clear -Y SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB NSR NRB0 CWF; dlia).
    carry ZU MUr WMr ltac:(ub DAP; clear -Y SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB NSR NRB0 CWF; dlia).
    carry STATS MUr WMr ltac:(ub DAT; ub DPT; rewrite ?upd_length, ?LSJ; clear -Y Y0 SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB NSR NRB0 CWF T0 T1 PA0 PA0a PA0b PA0c PA0d PA1 TIC; dlia).
    carry POST MUr WMr ltac:(clear -SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB SH1 SH2 SH4 NSR NRB0 CWF PA0 PA0a PA0b PA0c PA0d ASD ASDa ASDb; dlia).   (* [comment removed for export] *)
    carry SHU MUr WMr ltac:(clear -SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB MSR SH1 SH2 SH4 NSR NRB0 CWF PA0 PA0a PA0b PA0c PA0d SZP K0 ASD ASDa ASDb; Z.div_mod_to_equations; dlia).
    carry POST0 MUr WMr ltac:(rewrite SH5; ub MSM; clear -Y SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB MSR SH1 SH2 SH4 NSR NRB0 CWF PA0 PA0a PA0b PA0c PA0d SZP SZ8 K0 ASD ASDa ASDb; Z.div_mod_to_equations; dlia).
    assert (MUF : munch [(bv_unsigned sp - LARGE_STACK, bv_unsigned sp); (a, a + ms); (shad a, shad a + ms / 8);
                         (0xab408, 0xab668); (t + 2800, t + 3168);
                         (PA + 8 * nsec, PA + 8 * nsec + 8); (PA + 8 * nres, PA + 8 * nres + CW)]%Z m m9).
    { eapply munch_trans; [exact MUA|]. eapply munch_weaken; [| exact MU9]. unfold sub_fp. cbn [outside]. clear -MSB CWF. intros q Hq. lia. }
    assert (WMF : wmono asegs m m9) by (eapply wmono_trans; [exact WMA | exact WM9]).
    eapply (KONT1 a RNG' m9); [exact HFR | exact KQ |].
    unfold large_post. cbv zeta. change (needed_size n) with size. change (sec_map_size n) with ms.
    split; [exact FPLE|]. split; [exact BW|]. split; [exact AAL|]. split; [exact AHI0|]. split; [atop_facts; exact ACE|].
    split; [eapply munch_weaken; [| exact MUF]; unfold sub_fp, AINSTANCE; cbn [outside]; clear -CWF; intros q Hq; lia|]. split; [exact WMF|]. split; [exact MI9|]. split; [exact ST9|].
    split. { apply (proj2 (rw_cells_app asegs m9 a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 size); C8 (Z_to_bv 64 nsec)] [CB _ _])).
             split; [exact ZH9|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. exact ZP. }
    split; [exact ZU|].
    split; [exact POST|]. split; [exact SHU|]. split; [unfold fill_at; rewrite <- SH5; exact POST0|].
    split; [exact RCH|]. split; [exact RSCH|].
    split; [exact INS9|]. split; [exact SRT9|]. split; [exact JST9|]. split; [exact JBS9|]. split; [exact MTX9|]. split; [exact JGL9|].
    split; [eexists; split; [exact STATS| rewrite !upd_length; exact LSJ]|].
    split; [exact PAS9|].
    split; [left; split; [exact KQ| reflexivity]|].
    split; [exact NRB0|].
    eapply (large_cells_frame ctx t PA m m9); [exact LC | exact MUF | exact WMF | exact CXI |].
    (nd_pre (tclr_int_lem _ _ DAL ltac:(clear -AHIa; lia) ltac:(clear -AHId; atop_facts; lia)) 4%nat; intros kL DALk DALa DALb; nd_post). (nd_pre (tclr_int_lem _ _ DPL ltac:(clear -PA0a; lia) ltac:(clear -PA0d; atop_facts; lia)) 4%nat; intros kPL DPLk DPLa DPLb; nd_post).      (* [comment removed for export] *)
    ub DAC. ub DPC. ub CT2. unfold AIMG_HI, AIMG_LO. clear -DALk DALa DALb DPLk DPLa DPLb Y Y0 Y1 SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE CX0 CX1 PA0 PA0a PA0b PA0c PA0d PA1 SH1 SH2 MSB T0 T1 NSR NRB0 CWF CXI TIC CBND CBNDa CBNDb TBND TBNDa TBNDb.   (* [comment removed for export] *)
    repeat (apply Forall_cons; [cbn [fst snd]; first [right; lia | left; lia] |]). apply Forall_nil.
  Unshelve. all: try (apply ref_ro_addr_false; right; lia).
Qed.
End Zd2.
#[using="Type"] Lemma large_spec : forall RNG {R} (K : Z -> itree node (exc R)) (K2 : Z -> Z -> itree node (exc R))
    (Q : R -> footprint -> machine_state -> Prop) (FRESH : Z -> bool)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n ctx t PA nres nsec lo : Z) (sj : list word) (sorted : Z) (jstats jbsl jglob jslot : list byte),
  let size := needed_size n in let ms := sec_map_size n in
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - LARGE_STACK ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 0xab3d8 -> a1 = Z_to_bv 64 0xab648 ->      (* [comment removed for export] *) a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 8 ->
  1 <= n <= AREQMAX -> is_primary n = false ->
  large_cells ctx t PA m ->
  (* [comment removed for export] *)
  sclr ctx 65536 -> ctx + 4096 <= ATOP -> sclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  (* [comment removed for export] *)
  rw_cells asegs m 0xab408 [C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 nsec)] ->
  rw_cells asegs m 0xab418 [C1 (Z_to_bv 8 sorted)] ->
  rw_cells asegs m 0xab420 [CB 32 jstats] ->
  rw_cells asegs m 0xab440 [CB 512 jbsl] ->
  rw_cells asegs m 0xab640 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m 0xab658 [CB 16 jglob] ->
  (* [comment removed for export] *)
  ablk PA (PA + 8388608) -> PA + 8388608 <= ATOP -> PA mod 4096 = 0 ->      (* [comment removed for export] *)
  0 <= nsec <= nres -> nres mod 16384 = 0 -> nres <= 1048576 ->
  (nsec < nres -> rw_cells asegs m (PA + 8 * nsec) [CB 8 jslot]) ->
  (PA + 8388608 <= t \/ t + 4096 <= PA) -> (PA + 8388608 <= ctx \/ ctx + 4096 <= PA) ->
  tclr PA 8388608 ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG PA (8 * nres) ->
  AIMG_HI <= ctx -> iclr t 4096 ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  (forall a, FRESH a = true ->
        ablk a (a + ms)
     /\ (a + ms <= t \/ t + 4096 <= a) /\ (a + ms <= ctx \/ ctx + 4096 <= a) /\ (a + ms <= PA \/ PA + 8388608 <= a)
     /\ fill_at m (shad a) (ms / 8) 0
     /\ tclr a ms) ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  (forall a RNG' ms', FRESH a = false -> 0 < a -> a mod 4096 = 0 -> a + ms <= ATOP -> fp_le RNG RNG' ->
      implS asegs RNG' (K a) (epostF Q) ms') ->
  (* [comment removed for export] *)
  (forall a RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      FRESH a = true -> nsec <> nres -> large_post RNG sp a n ctx t PA nres nsec nres lo m RNG' m' ->
      implS asegs RNG' (K a) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (a + 4096)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  (* [comment removed for export] *)
  (forall a, FRESH a = true -> nsec = nres -> nres + 16384 <= 1048576 ->
      K a = ebind (enode (NMmap (PA + 8 * nres) 131072 3 50) (adec_mmap ATOP 131072 3)) (K2 a)) ->
  (* [comment removed for export] *)
  (forall a RNG' ms', FRESH a = true -> nsec = nres -> 1048576 < nres + 16384 -> implS asegs RNG' (K a) (epostF Q) ms') ->
  (forall a r RNG' ms', r <> PA + 8 * nres -> 0 < r -> r + 131072 <= ATOP -> implS asegs RNG' (K2 a r) (epostF Q) ms') ->
  (forall a RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      FRESH a = true -> nsec = nres -> large_post RNG sp a n ctx t PA nres nsec (nres + 16384) lo m RNG' m' ->
      implS asegs RNG' (K2 a (PA + 8 * nres)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (a + 4096)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (ebind (enode (NMmap 0 ms 3 34) (adec_mmap ATOP ms 3)) K) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 large_entry) fc None m (seg_rom asegs)).
Proof. exact large_spec__body. Qed.
End CANSEC2.
End TwB.
