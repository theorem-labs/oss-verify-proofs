(** * OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.GtDecPump — Q7 decode-face driver:
      [zr_decode_pump] terminates within its fuel, modulo the NAMED
      cross-call contract (q7-decode lane, zlib-rt, 2026-08-20)

    The two decode faces ([ZRepro_Decode_auto]/[_raw]) oblige
    [zr_decode wb x = Some rc] on arbitrary byte inputs.  This file
    proves the whole DRIVER side: the 137-byte chunked pump reaches an
    exit within [zr_decode_fuel x = 4*len+64] trips, given per-call
    facts stated as Section Variables (R6 option (a): each premise
    named per consumer, discharge route documented):

    - [Hreenter]/[Hshape]/[Hret] — the cross-call re-entry lap
      (an earlier development run; shapes sent consumer-first 2026-08-20, this file is
      the consuming instantiation that validates them).
    - [Hcall] — the cost/conservation sweep (this lane, GtDecCost,
      forthcoming): input-bit budget conservation (M1; fast node
      already Qed as [StepPres.if_model_pres]), the 258-bytes-per-
      budget-unit output cost (M2 — exactly the bound [ZRepro]'s fuel
      comment cites), window-sum bookkeeping (M3), signs, the [cpend]
      cap, and the carried [CostAux].  Interface v3 (2026-08-20): the
      cost quantity is [cpend] — u_length counted ONLY at the four
      match modes plus a 1-byte M_LIT flag — because raw u_length is
      input-backed at STORED/EXLEN (K would rise unbacked at their
      set-sites) and a LIT emission is length-free; and [CostAux]
      carries the selected-length-entry facts (extra <= 8 via
      2^e <= 256, length <= 258) across calls, without which LENEXT's
      gain cannot be charged at the 258 rate.  Both found by attempting
      the sweep (inhabitability-side check of the interface).
    - [Hdyn : DynTblOk] — the tree-wide residual, quantified as in
      StepReach/StepPres.

    THE POTENTIAL.  Phi := 2064*(8*|rem| + bits) + 8*pend, with
    2064 = 8*258.  Every continuing trip drops Phi by >= 32768 = 8*4096:
    - out-full trips: M2 couples wrote = 4096 against the budget delta
      at exactly the 258 rate, so the coupling cancels and the window's
      8*4096 survives — sign-agnostic in the delta, so the phantom-
      giveback case (used < 0, rem unchanged) needs no separate case;
    - starved trips (br_have' = 0): a CONTINUING starved trip has
      chunk = 137 (a partial chunk is the whole remaining input, whose
      full consumption empties rem and exits), so the budget drops
      >= 8*137 - 39 ([rc_bits39] at the NEXT entry, via [Hreenter] —
      no separate ask), and the pend rise is absolutely capped by
      pend' <= 98303.
    Fuel check: 32768*(4*len + 64) >= 2064*8*len + 32768, with margin. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Base.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import ZBitsIn.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Inftrees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import InflateFast.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Checksum.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import InflateThy.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import StepReach.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import StepPres.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Chunk.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Codec.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import GtInfTotal.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import DeclIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZRepro.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(** The next-call record, verbatim [zr_inf_call]'s shape. *)
Definition next_args (s : IState) (z : Strm) (inb : list Z)
                     (aout flush : Z) : InfArgs :=
  {| g_st := s; g_state_null := false; g_z := z;
     g_inbuf := zlist inb; g_next_in := 0;
     g_avail_in := zlen inb; g_in_null := false;
     g_outbuf := zzero; g_next_out := 0;
     g_avail_out := aout; g_out_null := false;
     g_flush := flush; g_walloc := true;
     g_wfresh := zzero |}.

Lemma zr_inf_call_model : forall flush s z inb aout,
  zr_inf_call flush s z inb aout
  = match inflate_model (next_args s z inb aout flush) with
    | None => None
    | Some r => Some (r_ret r, zlen inb - br_have (q_br (r_q r)),
                      q_st (r_q r), q_z (r_q r),
                      ob_slice (q_ob (r_q r)) 0 (o_put (q_ob (r_q r))))
    end.
Proof. reflexivity. Qed.

(** A carried (state, strm) pair is re-enterable at any in-cap fresh
    buffers. *)
Definition EntryOk (s : IState) (z : Strm) : Prop :=
  forall inb aout flush,
    (forall j, 0 <= zlist inb j < 256) ->
    (* 4294967285 = 2^32 - 11: rc_inbud has zero headroom at the u32
       ceiling and a re-entry carries up to 39 bits (rc_bits39), so the
       fresh-input cap gives back 5 bytes (an earlier development run catch, q7 ACK). *)
    0 <= zlen inb <= 4294967285 ->
    0 <= aout <= 4294967295 ->
    ReachSt (inf_st0 (next_args s z inb aout flush)).

(** Counted pending output: [u_length] is bits-backed output-in-flight
    ONLY at the four match modes (at STORED/EXLEN it is input-backed and
    charged at COPY/EXTRA consumption time); a decoded-but-unwritten
    literal ([M_LIT]) is one byte.  This is the quantity the 258-rate
    cost law conserves. *)
Definition cpend (s : IState) : Z :=
  match h_mode (s_hdr s) with
  | M_LENEXT | M_DIST | M_DISTEXT | M_MATCH => u_length (s_cur s)
  | M_LIT => 1
  | _ => 0
  end.

(** The sweep's own carried invariant (cross-call honest, like
    [rm_lens7]): the selected length entry's [lc_len_ok] content,
    surviving as state facts once the entry itself is gone.  Establishes
    at LEN's decode (relativised [lcode_len_bounded]); every other arm
    preserves it; vacuous at M_HEAD inits. *)
Definition CostAux (s : IState) : Prop :=
  (h_mode (s_hdr s) = M_LENEXT ->
     0 <= u_extra (s_cur s)
     /\ u_length (s_cur s) + Z.shiftl 1 (u_extra (s_cur s)) - 1 <= 258)
  /\ (h_mode (s_hdr s) = M_DIST \/ h_mode (s_hdr s) = M_DISTEXT
      \/ h_mode (s_hdr s) = M_MATCH ->
     u_length (s_cur s) <= 258).

(* ==========================================================================
   List/slice helpers (driver arithmetic).
   ========================================================================== *)

Lemma zlen_nonneg : forall l : list Z, 0 <= zlen l.
Proof. intros l. unfold zlen. lia. Qed.

Lemma zlen_firstn : forall n (l : list Z),
  zlen (firstn n l) = Z.min (Z.of_nat n) (zlen l).
Proof. intros n l. unfold zlen. rewrite length_firstn. lia. Qed.

Lemma zlen_skipn : forall n (l : list Z),
  zlen (skipn n l) = zlen l - Z.min (Z.of_nat n) (zlen l).
Proof. intros n l. unfold zlen. rewrite length_skipn. lia. Qed.

Lemma Forall_firstn' : forall (P : Z -> Prop) n (l : list Z),
  Forall P l -> Forall P (firstn n l).
Proof.
  intros P n. induction n as [|n IH]; intros l H; [constructor|].
  destruct l as [|a l]; cbn [firstn]; [constructor|].
  inversion H; subst. constructor; [assumption | apply IH; assumption].
Qed.

Lemma Forall_skipn' : forall (P : Z -> Prop) n (l : list Z),
  Forall P l -> Forall P (skipn n l).
Proof.
  intros P n. induction n as [|n IH]; intros l H; [exact H|].
  destruct l as [|a l]; cbn [skipn]; [constructor|].
  inversion H; subst. apply IH; assumption.
Qed.

Lemma zlen_ob_slice : forall o n, 0 <= n -> zlen (ob_slice o 0 n) = n.
Proof.
  intros o n Hn. unfold ob_slice, zlen.
  rewrite length_map, length_seq. lia.
Qed.

Lemma of_to_nat_max : forall x, Z.of_nat (Z.to_nat x) = Z.max 0 x.
Proof.
  intros x. destruct x as [|p|p]; [reflexivity| |cbn; lia].
  cbn [Z.to_nat]. rewrite positive_nat_Z. lia.
Qed.

Lemma zlist_nil_bytes : forall j, 0 <= zlist [] j < 256.
Proof. intros j. unfold zlist. destruct (Z.to_nat j); cbn; lia. Qed.

(* ==========================================================================
   The driver, Section-quantified over the named contract.
   ========================================================================== *)

Section DecPump.

Variable Hdyn : DynTblOk.

(** ASK 1 (an earlier development run): re-entry — G1 leave invariant + G2 writeback/uw
    transfer + G3 establishment, composed. *)
Variable Hreenter : forall c q0 q1,
    ReachSt q0 -> inf_step c q0 = InfLeave q1 ->
    (* the leaving call's ctx feeds [uw]'s alloc path: a fresh window's
       bytes become [rc_win] at the next entry (an earlier development run catch #7);
       every pump ctx is next_args-built, so n_wfresh = zzero. *)
    (forall j, 0 <= n_wfresh c j < 256) ->
    EntryOk (q_st (fst (inf_leave c q1))) (q_z (fst (inf_leave c q1))).

(** ASK 2 (an earlier development run): a Z_OK leave at Z_NO_FLUSH is input-starved or
    output-full; the leave's input count is nonnegative. *)
Variable Hshape : forall c q0 q1,
    ReachSt q0 -> inf_step c q0 = InfLeave q1 ->
    0 <= br_have (q_br (fst (inf_leave c q1)))
    /\ (n_flush c = Z_NO_FLUSH -> snd (inf_leave c q1) = Z_OK ->
        br_have (q_br (fst (inf_leave c q1))) = 0
        \/ o_left (q_ob (fst (inf_leave c q1))) = 0).

(** ASK 3 (an earlier development run): the direct-return arms never answer Z_OK. *)
Variable Hret : forall c q0 q1 rr,
    ReachSt q0 -> inf_step c q0 = InfRet q1 rr -> rr <> Z_OK.

(** This lane's sweep (GtDecCost): per-call conservation + cost at a
    reachable entry.  M1's fast node: [StepPres.if_model_pres]. *)
Variable Hcall : forall a,
    ReachSt (inf_st0 a) ->
    CostAux (g_st a) ->
    g_state_null a = false -> g_out_null a = false -> g_in_null a = false ->
    g_next_out a = 0 ->
    match inflate_model a with
    | None => True
    | Some r =>
        r_ret r = Z_OK ->
        8 * br_have (q_br (r_q r)) + s_bits (q_st (r_q r))
          <= 8 * g_avail_in a + s_bits (g_st a)
        /\ o_put (q_ob (r_q r)) + cpend (q_st (r_q r))
             + 258 * (8 * br_have (q_br (r_q r)) + s_bits (q_st (r_q r)))
           <= cpend (g_st a)
             + 258 * (8 * g_avail_in a + s_bits (g_st a))
        /\ 0 <= o_put (q_ob (r_q r))
        /\ o_put (q_ob (r_q r)) + o_left (q_ob (r_q r)) = g_avail_out a
        /\ 0 <= br_have (q_br (r_q r))
        /\ 0 <= s_bits (q_st (r_q r))
        /\ 0 <= cpend (q_st (r_q r))
        /\ cpend (q_st (r_q r)) <= 258
        /\ CostAux (q_st (r_q r))
    end.

Definition Phi (inp : list Z) (s : IState) : Z :=
  2064 * (8 * zlen inp + s_bits s) + 8 * cpend s.

(** One-step unfolding of the pump (fixpoint-on-S, reflexivity-safe). *)
Lemma zr_decode_pump_S :
  forall k s z inp,
    zr_decode_pump (S k) s z inp
    = let chunk := Z.min (zlen inp) 137 in
      match zr_inf_call Z_NO_FLUSH s z (firstn (Z.to_nat chunk) inp) 4096 with
      | None => None
      | Some (ret, used, s', z', out) =>
          if negb (Z.eqb ret Z_OK) then Some ret
          else
            let rem := skipn (Z.to_nat used) inp in
            if (Z.eqb (zlen rem) 0) && (Z.ltb (zlen out) 4096)
            then Some ret
            else zr_decode_pump k s' z' rem
      end.
Proof. reflexivity. Qed.

(** The pump answers within its fuel. *)
Lemma pump_total :
  forall f inp s z,
    EntryOk s z ->
    Forall (fun b => 0 <= b < 256) inp ->
    0 <= s_bits s ->
    CostAux s ->
    0 <= cpend s ->
    cpend s <= 258 ->
    zlen inp <= 67108864 ->
    32768 * Z.of_nat f >= Phi inp s + 32768 ->
    exists rc, zr_decode_pump f s z inp = Some rc.
Proof.
  induction f as [|f IH]; intros inp s z HE Hbytes Hbits Haux Hpend0 Hpendcap
    Hcap Hfuel.
  { exfalso. unfold Phi in Hfuel. pose proof (zlen_nonneg inp). lia. }
  rewrite zr_decode_pump_S. cbv zeta.
  set (chunk := Z.min (zlen inp) 137) in *.
  assert (Hchunk_eq : chunk = Z.min (zlen inp) 137) by reflexivity.
  set (inb := firstn (Z.to_nat chunk) inp) in *.
  assert (Hchunk0 : 0 <= chunk <= 137).
  { pose proof (zlen_nonneg inp). lia. }
  assert (Hlenb : zlen inb = chunk).
  { unfold inb. rewrite zlen_firstn. rewrite of_to_nat_max.
    pose proof (zlen_nonneg inp). lia. }
  (* the call answers, with the exit joint *)
  assert (HRentry : ReachSt (inf_st0 (next_args s z inb 4096 Z_NO_FLUSH))).
  { apply HE.
    - apply zlist_bytes. apply Forall_firstn'. exact Hbytes.
    - rewrite Hlenb. lia.
    - lia. }
  destruct (inflate_model_total_reach Hdyn (next_args s z inb 4096 Z_NO_FLUSH)
              eq_refl eq_refl eq_refl HRentry) as [r [Hm HJ]].
  assert (Hpc : CostAux (g_st (next_args s z inb 4096 Z_NO_FLUSH)))
    by exact Haux.
  pose proof (Hcall (next_args s z inb 4096 Z_NO_FLUSH) HRentry Hpc
                eq_refl eq_refl eq_refl eq_refl) as HC.
  rewrite Hm in HC.
  cbn [next_args g_avail_in g_avail_out g_st] in HC.
  rewrite Hlenb in HC.
  rewrite zr_inf_call_model, Hm. cbv beta iota.
  (* name the exit fields as atoms, keeping their equations for lia *)
  set (have' := br_have (q_br (r_q r))) in *.
  set (bits' := s_bits (q_st (r_q r))) in *.
  set (pend' := cpend (q_st (r_q r))) in *.
  set (oput' := o_put (q_ob (r_q r))) in *.
  set (oleft' := o_left (q_ob (r_q r))) in *.
  set (used := zlen inb - have') in *.
  assert (Hused_eq : used = chunk - have') by (unfold used; lia).
  set (out := ob_slice (q_ob (r_q r)) 0 oput') in *.
  destruct (Z.eqb_spec (r_ret r) Z_OK) as [Hok|Hnok]; cbn [negb].
  2: { eexists. reflexivity. }
  specialize (HC Hok).
  destruct HC as (HM1 & HM2 & Hoput0 & Hosum & Hhave0 & Hbits0' & Hpend0'
                  & Hpendcap' & Haux').
  assert (Hlout : zlen out = oput').
  { unfold out. apply zlen_ob_slice. exact Hoput0. }
  (* continuing trip: the exit joint must be a leave (Hret kills InfRet) *)
  destruct HJ as [HJ|HJ].
  2: { destruct HJ as (q0 & HR0 & E0). exfalso.
       exact (Hret _ _ _ _ HR0 E0 Hok). }
  destruct HJ as (q0 & q1 & HR0 & E0 & EL).
  assert (EL1 : q_st (fst (inf_leave (inf_ctx (next_args s z inb 4096 Z_NO_FLUSH)) q1))
                = q_st (r_q r)) by (rewrite EL; reflexivity).
  assert (EL1z : q_z (fst (inf_leave (inf_ctx (next_args s z inb 4096 Z_NO_FLUSH)) q1))
                = q_z (r_q r)) by (rewrite EL; reflexivity).
  assert (ELh : br_have (q_br (fst (inf_leave (inf_ctx (next_args s z inb 4096 Z_NO_FLUSH)) q1)))
                = have') by (rewrite EL; reflexivity).
  assert (ELo : o_left (q_ob (fst (inf_leave (inf_ctx (next_args s z inb 4096 Z_NO_FLUSH)) q1)))
                = oleft') by (rewrite EL; reflexivity).
  assert (EL2 : snd (inf_leave (inf_ctx (next_args s z inb 4096 Z_NO_FLUSH)) q1)
                = r_ret r) by (rewrite EL; reflexivity).
  (* leave shape *)
  destruct (Hshape _ _ _ HR0 E0) as [_ Hsh].
  rewrite ELh, ELo, EL2 in Hsh.
  specialize (Hsh eq_refl Hok).
  (* re-entry *)
  pose proof (Hreenter _ _ _ HR0 E0
                (fun j => ltac:(cbv [next_args inf_ctx n_wfresh g_wfresh
                                     zzero zconst]; lia))) as HE'.
  rewrite EL1, EL1z in HE'.
  (* bits' <= 39 via rc_bits39 at the next entry *)
  assert (Hbits39 : bits' <= 39).
  { pose proof (HE' [] 4096 Z_NO_FLUSH zlist_nil_bytes
                  ltac:(cbn; lia) ltac:(lia)) as HRn.
    destruct HRn as [HCn _].
    pose proof (rc_bits39 _ HCn) as HB.
    unfold inf_st0 in HB. cbn [next_args g_st] in HB.
    unfold bits'.
    destruct (h_mode (s_hdr (q_st (r_q r)))); cbn [q_br br_bits] in HB;
      exact HB. }
  set (rem := skipn (Z.to_nat used) inp).
  assert (Hlrem : zlen rem = zlen inp - Z.min (Z.max 0 used) (zlen inp)).
  { unfold rem. rewrite zlen_skipn, of_to_nat_max. reflexivity. }
  pose proof (zlen_nonneg inp) as Hlen0.
  destruct (Z.eqb_spec (zlen rem) 0) as [Hrem0|Hremn].
  - destruct (Z.ltb_spec (zlen out) 4096) as [Hlt|Hge]; cbn [andb].
    { eexists. reflexivity. }
    (* continuing: rem = 0, window full (oput' >= 4096) *)
    apply IH; [exact HE' | apply Forall_skipn'; exact Hbytes
               | exact Hbits0' | exact Haux' | exact Hpend0' | exact Hpendcap'
               | pose proof (zlen_nonneg rem); lia |].
    rewrite Hlout in Hge.
    unfold Phi in Hfuel |- *.
    change (s_bits (q_st (r_q r))) with bits'.
    change (cpend (q_st (r_q r))) with pend'.
    lia.
  - cbn [andb].
    apply IH; [exact HE' | apply Forall_skipn'; exact Hbytes
               | exact Hbits0' | exact Haux' | exact Hpend0' | exact Hpendcap'
               | rewrite Hlrem; lia |].
    unfold Phi in Hfuel |- *.
    change (s_bits (q_st (r_q r))) with bits'.
    change (cpend (q_st (r_q r))) with pend'.
    destruct Hsh as [Hstarv|Hofull].
    + (* starved: used = chunk; continuing forces chunk = 137 *)
      assert (H137 : chunk = 137).
      { destruct (Z.eqb_spec chunk (zlen inp)) as [He|Hne]; [|lia].
        exfalso. apply Hremn. lia. }
      lia.
    + (* out-full with rem <> 0: the M2 coupling, sign-agnostic *)
      assert (Hofull' : oput' = 4096) by lia.
      lia.
Qed.

(** Driver-side face shape: any concrete init whose reset state carries
    zero bits and zero pending length. *)
Lemma zr_decode_terminates :
  forall wb z0 s0,
    inflateInit2 z_fresh state_fresh wb = Some (z0, s0) ->
    s_bits s0 = 0 ->
    h_mode (s_hdr s0) = M_HEAD ->
    forall x, ZR_Input x -> exists rc, zr_decode wb x = Some rc.
Proof.
  intros wb z0 s0 HI Hb0 Hm0 x [Hbytes Hcap].
  assert (Hc0 : cpend s0 = 0) by (unfold cpend; rewrite Hm0; reflexivity).
  unfold zr_decode. rewrite HI.
  apply (pump_total (zr_decode_fuel x) x s0 z0).
  - intros inb aout flush Hb Hain Haout.
    apply (reach_entry_fresh z0 s0 wb (next_args s0 z0 inb aout flush)
             HI eq_refl Hb).
    + cbn [next_args g_avail_in]. lia.
    + cbn [next_args g_avail_out]. exact Haout.
    + intros j. cbn [next_args g_outbuf]. cbv [zzero zconst]. lia.
  - exact Hbytes.
  - lia.
  - split; [intros HmL | intros HmL]; exfalso;
      [rewrite Hm0 in HmL; discriminate
      | destruct HmL as [HmL|[HmL|HmL]]; rewrite Hm0 in HmL; discriminate].
  - lia.
  - lia.
  - unfold ZR_MAX_INPUT in Hcap. lia.
  - unfold Phi, zr_decode_fuel. rewrite Hb0, Hc0.
    pose proof (zlen_nonneg x) as Hx0.
    assert (Hid : Z.of_nat (Z.to_nat (zlen x)) = zlen x)
      by (rewrite of_to_nat_max; lia).
    rewrite Nat2Z.inj_add, Nat2Z.inj_mul, Hid.
    unfold ZR_MAX_INPUT in Hcap. cbn [Z.of_nat]. lia.
Qed.

(** The two faces, Section-conditional: everything between this file
    and the open [ZRepro_Decode_*] Definitions is the Section contract
    (DynTblOk; an earlier development run's three; this lane's Hcall). *)
Lemma decode_raw_face : ZRepro_Decode_raw.
Proof.
  unfold ZRepro_Decode_raw, ZR_DecodeTerminates.
  destruct (inflateInit2 z_fresh state_fresh (-15)) as [[z0 s0]|] eqn:EI.
  2: { exfalso. vm_compute in EI. discriminate. }
  assert (H0 : s_bits s0 = 0 /\ h_mode (s_hdr s0) = M_HEAD).
  { revert EI. vm_compute. intros E. injection E as E1 E2. subst.
    split; reflexivity. }
  intros x Hx.
  exact (zr_decode_terminates (-15) z0 s0 EI (proj1 H0) (proj2 H0) x Hx).
Qed.

Lemma decode_auto_face : ZRepro_Decode_auto.
Proof.
  unfold ZRepro_Decode_auto, ZR_DecodeTerminates.
  destruct (inflateInit2 z_fresh state_fresh 47) as [[z0 s0]|] eqn:EI.
  2: { exfalso. vm_compute in EI. discriminate. }
  assert (H0 : s_bits s0 = 0 /\ h_mode (s_hdr s0) = M_HEAD).
  { revert EI. vm_compute. intros E. injection E as E1 E2. subst.
    split; reflexivity. }
  intros x Hx.
  exact (zr_decode_terminates 47 z0 s0 EI (proj1 H0) (proj2 H0) x Hx).
Qed.

End DecPump.
