(** * Bridge.IRelInfl — INTERFACE (part C lead): the inflate state relation, S5 vs RT.

    S5 runs inflate on an [iw] = [inflate_state] (36 fields) + [icall] (the
    stream fields) + [iregs] (the C locals next/have/put/left/hold/bits/in/
    out/ret), with LOAD/RESTORE copying between them
    ([Z/InflateState.v:155,357,413,443]).  RT runs on an [InfSt] = [IState]
    (five sub-records [IHdr]/[IWin]/[ICur]/[ITab]/[IBld] plus hold/bits) +
    [Strm] + the bit reader [BR] + the output buffer [OB] + in/out/ret
    ([Spec/PngModel/Inflate.v:537,714]).  RT keeps one live copy of
    next/have/put/left in [BR]/[OB], so INSIDE the loop it relates to S5's
    registers, not to S5's [icall].

      [ist_core_rel]  the five [IState] clusters against [inflate_state]
      [is_rel]        between calls (hold/bits in the state)
      [iw_rel]        inside the loop (hold/bits, input and output in the
                      registers)

    Not related, on purpose: [msg] (the two models number the messages
    differently; the harness never reads msg), the allocation block ids,
    and [ic_next_in]/[ic_avail_in]/[ic_next_out]/[ic_avail_out] inside the
    loop (stale until RESTORE, as in the C).

    Ownership: the part C lead.  Groups import this file and do not edit it;
    an interface change goes through the lead (PAIR-GROUPS.md). *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require InflateState.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base ZBitsIn Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module IS := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.InflateState.
Module RI := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel.Inflate.
Module RB := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel.ZBitsIn.

(** [inftrees.h] ENOUGH (= ENOUGH_LENS + ENOUGH_DISTS = 852 + 592), the
    lens array (320) and the work array (288): S5's array lengths. *)
Definition ENOUGH : Z := 1444.
Definition NLENS : Z := 320.
Definition NWORK : Z := 288.

Definition codeptr_rel (c : IS.codeptr) (r : RI.TblRef) : Prop :=
  match c, r with
  | IS.CDyn o, RI.TRcodes o' => o = o'
  | IS.CLenfix, RI.TRlenfix => True
  | IS.CDistfix, RI.TRdistfix => True
  | _, _ => False
  end.

Definition hdr_rel (s : IS.inflate_state) (h : RI.IHdr) : Prop :=
  IS.is_mode s = RI.m_val (RI.h_mode h) /\ IS.is_last s = RI.h_last h
  /\ IS.is_wrap s = RI.h_wrap h /\ IS.is_havedict s = RI.h_havedict h
  /\ IS.is_flags s = RI.h_flags h /\ IS.is_dmax s = RI.h_dmax h
  /\ IS.is_check s = RI.h_check h /\ IS.is_total s = RI.h_total h
  /\ IS.is_head s = RI.h_head h.

(** The window: allocated on both sides or on neither; once allocated, S5's
    array has [2^wbits] slots and agrees with RT's on [[0, wsize)]. *)
Definition win_rel (s : IS.inflate_state) (w : RI.IWin) : Prop :=
  IS.is_wbits s = RI.w_wbits w /\ IS.is_wsize s = RI.w_wsize w
  /\ IS.is_whave s = RI.w_whave w /\ IS.is_wnext s = RI.w_wnext w
  /\ (IS.is_window_blk s <> None <-> RI.w_alloc w = true)
  /\ (RI.w_alloc w = true ->
        arr_len (IS.is_window s) = Z.shiftl 1 (RI.w_wbits w)
        /\ RI.w_wsize w <= arr_len (IS.is_window s)
        /\ arr_rel (IS.is_window s) (RI.w_win w) 0 (RI.w_wsize w)).

(** [back] is a signed int in S5 and unbounded in RT; it is a debugging
    counter the harness never observes, so only its 32-bit image is related. *)
Definition cur_rel (s : IS.inflate_state) (u : RI.ICur) : Prop :=
  IS.is_length s = RI.u_length u /\ IS.is_offset s = RI.u_offset u
  /\ IS.is_extra s = RI.u_extra u /\ IS.is_back s = swrap32 (RI.u_back u)
  /\ IS.is_was s = RI.u_was u.

Definition tab_rel (s : IS.inflate_state) (t : RI.ITab) : Prop :=
  codeptr_rel (IS.is_lencode s) (RI.t_lencode t)
  /\ codeptr_rel (IS.is_distcode s) (RI.t_distcode t)
  /\ IS.is_lenbits s = RI.t_lenbits t /\ IS.is_distbits s = RI.t_distbits t
  /\ IS.is_next s = RI.t_next t
  /\ arr_len (IS.is_codes s) = ENOUGH
  /\ tbl_rel (IS.is_codes s) (RI.t_codes t) 0 ENOUGH
  /\ IS.is_sane s = RI.t_sane t.

Definition bld_rel (s : IS.inflate_state) (b : RI.IBld) : Prop :=
  IS.is_ncode s = RI.b_ncode b /\ IS.is_nlen s = RI.b_nlen b
  /\ IS.is_ndist s = RI.b_ndist b /\ IS.is_have s = RI.b_have b
  /\ arr_len (IS.is_lens s) = NLENS /\ arr_rel (IS.is_lens s) (RI.b_lens b) 0 NLENS
  /\ arr_len (IS.is_work s) = NWORK.

Definition ist_core_rel (s : IS.inflate_state) (st : RI.IState) : Prop :=
  hdr_rel s (RI.s_hdr st) /\ win_rel s (RI.s_win st) /\ cur_rel s (RI.s_cur st)
  /\ tab_rel s (RI.s_tab st) /\ bld_rel s (RI.s_bld st).

(** Between calls: hold and bits live in the state. *)
Definition is_rel (s : IS.inflate_state) (st : RI.IState) : Prop :=
  ist_core_rel s st /\ IS.is_hold s = RI.s_hold st /\ IS.is_bits s = RI.s_bits st.

(** The stream fields both models keep outside the loop locals. *)
Definition zstrm_rel (c : IS.icall) (z : RI.Strm) : Prop :=
  IS.ic_total_in c = RI.z_tin z /\ IS.ic_total_out c = RI.z_tout z
  /\ IS.ic_adler c = RI.z_adler z /\ IS.ic_data_type c = RI.z_dtype z.

(** Inside the loop: S5's registers against RT's [BR]/[OB]/locals.  The
    input array is the call's whole input ([ic_input], absolute indices
    from 0, as RT's [br_in]); the output array agrees up to [put]. *)
Definition iw_rel (w : IS.iw) (q : RI.InfSt) : Prop :=
  let s := IS.w_s w in let c := IS.w_c w in let r := IS.w_r w in
  let b := RI.q_br q in let o := RI.q_ob q in
  ist_core_rel s (RI.q_st q)
  /\ IS.ir_hold r = RB.br_hold b /\ IS.ir_bits r = RB.br_bits b
  /\ IS.ir_next r = RB.br_next b /\ IS.ir_have r = RB.br_have b
  /\ 0 <= IS.ir_next r /\ 0 <= IS.ir_have r
  /\ arr_len (IS.ic_input c) = IS.ir_next r + IS.ir_have r
  /\ arr_rel (IS.ic_input c) (RB.br_in b) 0 (arr_len (IS.ic_input c))
  /\ IS.ir_put r = RI.o_put o /\ IS.ir_left r = RI.o_left o
  /\ 0 <= IS.ir_put r /\ 0 <= IS.ir_left r
  /\ arr_len (IS.ic_outbuf c) = IS.ir_put r + IS.ir_left r
  /\ arr_rel (IS.ic_outbuf c) (RI.o_buf o) 0 (IS.ir_put r)
  /\ zstrm_rel c (RI.q_z q)
  /\ IS.ir_in r = RI.q_in q /\ IS.ir_out r = RI.q_out q /\ IS.ir_ret r = RI.q_ret q.

(* ------------------------------------------------------------------------- *)
(* Checkers                                                                  *)
(* ------------------------------------------------------------------------- *)

Definition codeptr_relb (c : IS.codeptr) (r : RI.TblRef) : bool :=
  match c, r with
  | IS.CDyn o, RI.TRcodes o' => o =? o'
  | IS.CLenfix, RI.TRlenfix => true
  | IS.CDistfix, RI.TRdistfix => true
  | _, _ => false
  end.

Lemma codeptr_relb_sound : forall c r, codeptr_relb c r = true -> codeptr_rel c r.
Proof. intros [o| |] [o'| |]; cbn; try discriminate; try tauto. apply Z.eqb_eq. Qed.

Definition hdr_relb (s : IS.inflate_state) (h : RI.IHdr) : bool :=
  (IS.is_mode s =? RI.m_val (RI.h_mode h)) && (IS.is_last s =? RI.h_last h)
  && (IS.is_wrap s =? RI.h_wrap h) && (IS.is_havedict s =? RI.h_havedict h)
  && (IS.is_flags s =? RI.h_flags h) && (IS.is_dmax s =? RI.h_dmax h)
  && (IS.is_check s =? RI.h_check h) && (IS.is_total s =? RI.h_total h)
  && (IS.is_head s =? RI.h_head h).

Definition win_relb (s : IS.inflate_state) (w : RI.IWin) : bool :=
  (IS.is_wbits s =? RI.w_wbits w) && (IS.is_wsize s =? RI.w_wsize w)
  && (IS.is_whave s =? RI.w_whave w) && (IS.is_wnext s =? RI.w_wnext w)
  && Bool.eqb (match IS.is_window_blk s with Some _ => true | None => false end) (RI.w_alloc w)
  && (negb (RI.w_alloc w)
      || ((arr_len (IS.is_window s) =? Z.shiftl 1 (RI.w_wbits w))
          && (RI.w_wsize w <=? arr_len (IS.is_window s))
          && arr_relb (IS.is_window s) (RI.w_win w) 0 (RI.w_wsize w))).

Definition cur_relb (s : IS.inflate_state) (u : RI.ICur) : bool :=
  (IS.is_length s =? RI.u_length u) && (IS.is_offset s =? RI.u_offset u)
  && (IS.is_extra s =? RI.u_extra u) && (IS.is_back s =? swrap32 (RI.u_back u))
  && (IS.is_was s =? RI.u_was u).

Definition tab_relb (s : IS.inflate_state) (t : RI.ITab) : bool :=
  codeptr_relb (IS.is_lencode s) (RI.t_lencode t)
  && codeptr_relb (IS.is_distcode s) (RI.t_distcode t)
  && (IS.is_lenbits s =? RI.t_lenbits t) && (IS.is_distbits s =? RI.t_distbits t)
  && (IS.is_next s =? RI.t_next t)
  && (arr_len (IS.is_codes s) =? ENOUGH)
  && tbl_relb (IS.is_codes s) (RI.t_codes t) 0 ENOUGH
  && (IS.is_sane s =? RI.t_sane t).

Definition bld_relb (s : IS.inflate_state) (b : RI.IBld) : bool :=
  (IS.is_ncode s =? RI.b_ncode b) && (IS.is_nlen s =? RI.b_nlen b)
  && (IS.is_ndist s =? RI.b_ndist b) && (IS.is_have s =? RI.b_have b)
  && (arr_len (IS.is_lens s) =? NLENS) && arr_relb (IS.is_lens s) (RI.b_lens b) 0 NLENS
  && (arr_len (IS.is_work s) =? NWORK).

Definition is_relb (s : IS.inflate_state) (st : RI.IState) : bool :=
  hdr_relb s (RI.s_hdr st) && win_relb s (RI.s_win st) && cur_relb s (RI.s_cur st)
  && tab_relb s (RI.s_tab st) && bld_relb s (RI.s_bld st)
  && (IS.is_hold s =? RI.s_hold st) && (IS.is_bits s =? RI.s_bits st).

Ltac irelb_split H :=
  repeat match type of H with
  | _ && _ = true => apply andb_prop in H; destruct H as [H ?H]
  end.

Ltac irelb_atoms :=
  repeat match goal with
  | H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
  | H : (_ <=? _) = true |- _ => apply Z.leb_le in H
  | H : arr_relb _ _ _ _ = true |- _ => apply arr_relb_sound in H
  | H : tbl_relb _ _ _ _ = true |- _ => apply tbl_relb_sound in H
  | H : codeptr_relb _ _ = true |- _ => apply codeptr_relb_sound in H
  end.

Lemma is_relb_sound : forall s st, is_relb s st = true -> is_rel s st.
Proof.
  intros s st H. unfold is_relb in H. irelb_split H.
  unfold is_rel, ist_core_rel. split; [|split; irelb_atoms; assumption].
  split; [|split; [|split; [|split]]].
  - unfold hdr_relb in H. irelb_split H. irelb_atoms. unfold hdr_rel. repeat split; assumption.
  - match goal with Hw : win_relb _ _ = true |- _ => unfold win_relb in Hw; irelb_split Hw end.
    irelb_atoms. unfold win_rel.
    match goal with Hb : Bool.eqb _ _ = true |- _ => apply Bool.eqb_prop in Hb end.
    split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split.
    + destruct (IS.is_window_blk s); cbn in *; subst; split; congruence.
    + intros Ha. match goal with Ho : negb _ || _ = true |- _ => apply orb_prop in Ho; destruct Ho as [Hn|Hy] end.
      * rewrite Ha in Hn. discriminate.
      * irelb_split Hy. irelb_atoms. repeat split; assumption.
  - match goal with Hc : cur_relb _ _ = true |- _ => unfold cur_relb in Hc; irelb_split Hc end.
    irelb_atoms. unfold cur_rel. repeat split; assumption.
  - match goal with Ht : tab_relb _ _ = true |- _ => unfold tab_relb in Ht; irelb_split Ht end.
    irelb_atoms. unfold tab_rel. repeat split; assumption.
  - match goal with Hb : bld_relb _ _ = true |- _ => unfold bld_relb in Hb; irelb_split Hb end.
    irelb_atoms. unfold bld_rel. repeat split; assumption.
Qed.
