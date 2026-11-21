(** * Bridge.Infl.ITopEntry — the start of the harness's inflate call, both models (pair I1 and
    the call prologue).

    Part of ITop.  The harness's
    uncompress makes its first inflate call on S5's fresh state [ZApiInst.is0] with the whole
    input [enc] and [avail_out = n]; S5's [inflate_m] starts its loop from
    [RefInflate_runA.W0 is0 zc] (LOAD of the call into the registers).  RT's [zr_inflate] runs
    [inflate_model] on the state [inflateInit2] makes ([rt_st0]) with the same input and a
    zeroed output buffer, starting its loop from [inf_st0].  The two loop-entry states satisfy
    group I's loop invariant [IInv.inv] (mode HEAD), and RT's call context is [ctx_rel FL]. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require InflateState Inflate ZApiInst RefInflate_runA.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Chunk ZBitsIn Inflate Codec.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelInfl IFuelInfl.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.Infl Require Import IInv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module SI := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.Inflate.
Module ZAI := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.ZApiInst.
Module RA := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.RefInflate_runA.
Module RCo := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel.Codec.
Module CH := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel.Chunk.

(* ------------------------------------------------------------------------- *)
(* The two calls                                                             *)
(* ------------------------------------------------------------------------- *)

(** RT's stream and state after [inflateInit2] at windowBits 15. *)
Definition rt_z0 : RI.Strm :=
  match RI.inflateInit2 RCo.z_fresh RCo.state_fresh 15 with Some (z, _) => z | None => RCo.z_fresh end.
Definition rt_st0 : RI.IState :=
  match RI.inflateInit2 RCo.z_fresh RCo.state_fresh 15 with Some (_, s) => s | None => RCo.state_fresh end.

Lemma rt_init_eq : RI.inflateInit2 RCo.z_fresh RCo.state_fresh 15 = Some (rt_z0, rt_st0).
Proof. vm_compute. reflexivity. Qed.

(* Keep [cbn] from evaluating [inflateInit2] inside a goal; the facts below are by [vm_compute]. *)
Arguments rt_z0 : simpl never.
Arguments rt_st0 : simpl never.

(** S5's call: the harness's [zic_inflate enc zi_init n]. *)
Definition hc_call (enc : list Z) (n : Z) : ZCall := mkZCall enc n ZAI.iz0.

(** RT's call: [ZRepro.zr_inf_call 0 s z enc n]'s arguments, verbatim; [rt_args] at the
    state [inflateInit2] makes.  (Proofs about the call keep [z]/[s] abstract where they can:
    the kernel would otherwise evaluate RT's inflate on the concrete state while checking a
    conversion.) *)
Definition rt_args' (z : RI.Strm) (s : RI.IState) (enc : list Z) (n : Z) : RI.InfArgs :=
  {| RI.g_st := s; RI.g_state_null := false; RI.g_z := z;
     RI.g_inbuf := RBa.zlist enc; RI.g_next_in := 0;
     RI.g_avail_in := CH.zlen enc; RI.g_in_null := false;
     RI.g_outbuf := RBa.zzero; RI.g_next_out := 0;
     RI.g_avail_out := n; RI.g_out_null := false;
     RI.g_flush := 0; RI.g_walloc := true;
     RI.g_wfresh := RBa.zzero |}.

Definition rt_args (enc : list Z) (n : Z) : RI.InfArgs := rt_args' rt_z0 rt_st0 enc n.

(* ------------------------------------------------------------------------- *)
(* Closed facts of the two fresh states                                      *)
(* ------------------------------------------------------------------------- *)

Lemma is0_facts :
  IS.is_mode ZAI.is0 = IS.HEAD /\ IS.is_hold ZAI.is0 = 0 /\ IS.is_bits ZAI.is0 = 0
  /\ IS.is_total ZAI.is0 = 0 /\ IS.is_wrap ZAI.is0 = 5 /\ IS.is_wbits ZAI.is0 = 15
  /\ IS.is_havedict ZAI.is0 = 0 /\ IS.is_sane ZAI.is0 = 1
  /\ IS.is_wsize ZAI.is0 = 0 /\ IS.is_whave ZAI.is0 = 0 /\ IS.is_wnext ZAI.is0 = 0
  /\ IS.is_window_blk ZAI.is0 = None /\ SI.inflateStateCheck ZAI.is0 = false.
Proof. repeat split; vm_compute; reflexivity. Qed.

Lemma s_entry_is0 : RA.s_entry ZAI.is0 = ZAI.is0.
Proof.
  unfold RA.s_entry. replace (IS.is_mode ZAI.is0 =? IS.TYPE) with false by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma iz0_facts :
  zs_total_in ZAI.iz0 = RI.z_tin rt_z0 /\ zs_total_out ZAI.iz0 = RI.z_tout rt_z0
  /\ zs_adler ZAI.iz0 = RI.z_adler rt_z0 /\ zs_data_type ZAI.iz0 = RI.z_dtype rt_z0
  /\ zs_total_out ZAI.iz0 = 0.
Proof. repeat split; vm_compute; reflexivity. Qed.

Lemma rt_st0_facts :
  RI.h_mode (RI.s_hdr rt_st0) = RI.M_HEAD /\ RI.s_hold rt_st0 = 0 /\ RI.s_bits rt_st0 = 0
  /\ (forall i, code_rng (RI.t_codes (RI.s_tab rt_st0) i)).
Proof.
  split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  intros i. assert (E : RI.t_codes (RI.s_tab rt_st0) i = RBa.mkCode 0 0 0) by (vm_compute; reflexivity).
  rewrite E. unfold code_rng. cbn [RBa.c_op RBa.c_bits RBa.c_val]. lia.
Qed.

Lemma is0_related : is_rel ZAI.is0 rt_st0.
Proof. apply is_relb_sound. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------------- *)
(* Arrays                                                                    *)
(* ------------------------------------------------------------------------- *)

(** S5's input array reads as RT's [zlist] at every nonnegative index (both 0 past the end). *)
Lemma arr_get_of_list_all : forall l j, 0 <= j -> arr_get (arr_of_list l) j = RBa.zlist l j.
Proof.
  intros l j Hj. unfold arr_of_list, parr_of_list. rewrite (arr_get_upd l _ 0 j 0).
  unfold arr_inb. rewrite arr_len_make, arr_get_make, Z.add_0_l, Z.sub_0_r. unfold RBa.zlist.
  destruct (Z.leb_spec 0 j) as [_|]; [|lia].
  destruct (Z.ltb_spec j (zlength l)) as [Hl|Hl]; cbn [andb].
  - reflexivity.
  - symmetry. apply nth_overflow. unfold zlength in Hl. lia.
Qed.

Lemma zlist_byte : forall l, Forall (fun b => 0 <= b < 256) l -> forall j, 0 <= RBa.zlist l j < 256.
Proof.
  intros l Hb j. unfold RBa.zlist.
  destruct (Nat.lt_ge_cases (Z.to_nat j) (length l)) as [H|H].
  - rewrite Forall_forall in Hb. apply Hb, nth_In, H.
  - rewrite nth_overflow by exact H. lia.
Qed.

(* ------------------------------------------------------------------------- *)
(* The loop-entry states                                                     *)
(* ------------------------------------------------------------------------- *)

Lemma rt_q0_eq : forall enc n,
  RI.inf_st0 (rt_args enc n)
  = {| RI.q_st := rt_st0; RI.q_z := rt_z0;
       RI.q_br := {| RB.br_in := RBa.zlist enc; RB.br_have := CH.zlen enc; RB.br_next := 0;
                     RB.br_hold := 0; RB.br_bits := 0 |};
       RI.q_ob := {| RI.o_buf := RBa.zzero; RI.o_put := 0; RI.o_left := n |};
       RI.q_in := CH.zlen enc; RI.q_out := n; RI.q_ret := RBa.Z_OK |}.
Proof.
  intros enc n. pose proof rt_st0_facts as (Rm & Rh & Rb & _).
  unfold RI.inf_st0, rt_args, rt_args'. cbn [RI.g_st RI.g_z RI.g_inbuf RI.g_next_in RI.g_avail_in
    RI.g_outbuf RI.g_next_out RI.g_avail_out].
  rewrite Rm, Rh, Rb. reflexivity.
Qed.

Theorem entry_ctx : forall enc n, ctx_rel FL (RI.inf_ctx (rt_args enc n)).
Proof. intros enc n. split; reflexivity. Qed.

Theorem entry_inv : forall enc n,
  Forall (fun b => 0 <= b < 256) enc -> zlength enc < 2 ^ 32 -> 0 <= n < 2 ^ 31 ->
  inv (RA.W0 ZAI.is0 (hc_call enc n)) (RI.inf_st0 (rt_args enc n)).
Proof.
  intros enc n Hb Hlen Hn.
  pose proof is0_facts as (Hm & Hh & Hbt & Htot & Hwr & Hwb & Hhd & Hsn & Hws & Hwh & Hwn & Hblk & _).
  pose proof rt_st0_facts as (Rm & _ & _ & Rc).
  pose proof iz0_facts as (Z1 & Z2 & Z3 & Z4 & Z5).
  pose proof is0_related as Hrel.
  pose proof (zlength_nonneg enc) as Hl0.
  rewrite rt_q0_eq. unfold RA.W0, hc_call. rewrite s_entry_is0, Hh, Hbt.
  split.
  2:{ unfold imode, RI.q_mode. cbn [RI.q_st]. rewrite Rm. exact I. }
  unfold icore, iw_rel. cbv zeta.
  cbn [IS.w_s IS.w_c IS.w_r IS.ir_hold IS.ir_bits IS.ir_next IS.ir_have IS.ir_put IS.ir_left
       IS.ir_in IS.ir_out IS.ir_ret IS.icall_of_zcall IS.ic_input IS.ic_outbuf IS.ic_total_out
       zc_input zc_avail_out zc_strm
       RI.q_st RI.q_br RI.q_ob RI.q_z RI.q_in RI.q_out RI.q_ret
       RB.br_hold RB.br_bits RB.br_next RB.br_have RB.br_in RI.o_put RI.o_left RI.o_buf].
  split; [split; [exact (proj1 Hrel)|]|].
  - (* the registers against BR / OB *)
    rewrite arr_len_of_list.
    repeat split; try reflexivity; try lia.
    + intros i Hi. apply arr_get_of_list_all. lia.
    + intros i Hi. lia.
  - repeat split.
    all: try first
      [ lia
      | reflexivity
      | (intros i Hi; split; [apply arr_get_of_list_all; exact Hi | apply zlist_byte; exact Hb])
      | (intros i Hi; rewrite arr_get_make; reflexivity)
      | exact Z5 | exact Htot | exact Hwr | exact Hwb | exact Hhd | exact Hsn
      | exact Hws | exact Hwh | exact Hwn | exact Hblk
      | (intros H; exfalso; apply H; exact Hm)
      | apply Rc
      | (match goal with |- context [RI.w_win (RI.s_win rt_st0) ?i] =>
           assert (E : RI.w_win (RI.s_win rt_st0) i = 0) by (vm_compute; reflexivity); lia end)
      | (cbv [RBa.zzero RBa.zconst]; lia)
      | (apply arr_get_of_list_all; assumption)
      | (match goal with |- context [RBa.zlist ?l ?i] => pose proof (zlist_byte l Hb i); lia end) ].
Qed.

Print Assumptions entry_inv.
Print Assumptions entry_ctx.
