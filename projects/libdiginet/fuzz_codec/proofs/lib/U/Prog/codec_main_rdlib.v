(** The kind-independent part of the reader segments of the UBSan LLVMFuzzerTestOneInput walk: input
    byte reads, the driver of a read chain, the range of an assembled value, the record a reader
    fills, the machine state at a reader cut, and the lemma that hands a finished record to run(). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require Import codec_cells codec_img codec_main_inv.
Import ListNotations.
Open Scope Z_scope.

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

(** ---- input bytes ---- *)

(** One input byte at any cut: the walk writes only inside the stack window, so munch keeps it. *)
Lemma data_read1 : forall E m (a : word), env_ok E ->
  munch [(bv_unsigned (c_sp E) - 640, bv_unsigned (c_sp E))] (c_m E) m ->
  bv_unsigned (c_p E) <= bv_unsigned a < bv_unsigned (c_p E) + Z.of_nat (length (c_data E)) ->
  ov_read_bytes rsegs m a 1 = Some [nth (Z.to_nat (bv_unsigned a - bv_unsigned (c_p E))) (c_data E) (Z_to_bv 8 0)].
Proof.
  intros E m a HE MU Ha.
  pose proof (data_at E m HE MU) as HD.
  rewrite <- (bytes_at_byte m (bv_unsigned (c_p E)) (c_data E) (bv_unsigned a - bv_unsigned (c_p E)) HD) by lia.
  f_equal. unfold wa. rewrite <- (Z_to_bv_bv_unsigned a) at 1. f_equal. lia.
Qed.

(** The stepper's hook for a one-byte load from the input: it rewrites with [data_read1], the
    address range by lia from the cursor facts in the context. Every file that imports this one
    gets it through [solve_load]. *)
Ltac solve_load_data :=
  match goal with
  | |- context [ov_read_bytes rsegs ?m ?a 1] =>
    match goal with
    | HE : env_ok ?e, MU : munch _ (c_m ?e) m |- _ =>
      rewrite (data_read1 e m a HE MU) by (rewrite ?unsigned_lit by lia; lia)
    end
  end; load_post.
Ltac solve_load ::= first [ solve_load_base | solve_load_image | solve_load_data ].

(** ---- the driver of a read chain ---- *)

(** A conditional branch whose outcome the context decides (an in.n test or a UBSan trap edge):
    keep the feasible side, refute the other by lia. *)
Ltac decide_br :=
  let H := fresh "BR" in if_cases H; zify_cond H; try (exfalso; lia); try clear H.

(** An input byte read into a register becomes a variable [b] with [Hb : 0 <= bv_unsigned b < 256]. *)
Ltac gen_bytes :=
  repeat match goal with
  | |- context [nth ?k (c_data ?e) ?d] =>
      let b := fresh "b" in let Hb := fresh "Hb" in
      generalize (bv_unsigned_in_range 8 (nth k (c_data e) d)); generalize (nth k (c_data e) d);
      intros b Hb; change (bv_modulus 8) with 256 in Hb
  end.

(** Step to the literal pc [stop], deciding every branch on the way. It stops silently on an
    undecided branch or an instruction [step] cannot run, so the next tactic shows where. *)
Ltac drive stop :=
  repeat lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 stop) _ _ _ _) => fail
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => decide_br
  | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep; gen_bytes
  end.

(** The bytes left when a u32 read starts: none, one to three, or a whole u32. Split on it, then
    [subst] the literal cases, so every in.n test of the chain is decided. *)
Lemma rem_cases : forall rem, 0 <= rem -> rem = 0 \/ rem = 1 \/ rem = 2 \/ rem = 3 \/ 4 <= rem.
Proof. intros. lia. Qed.

(** ---- the range of an assembled value ---- *)

(** A shifted value is below [2 ^ k] when the value is below [2 ^ (k - s)]. *)
Lemma bnd_shl : forall x s k j, 0 <= s -> k - s = j -> 0 <= x < 2 ^ j -> 0 <= Z.shiftl x s < 2 ^ k.
Proof.
  intros x s k j Hs Hj [H0 H1]. rewrite Z.shiftl_mul_pow2 by lia.
  assert (Hj0 : 0 <= j).
  { destruct (Z.lt_ge_cases j 0) as [Hn|Hn]; [rewrite Z.pow_neg_r in H1 by lia; lia | lia]. }
  replace k with (j + s) by lia. rewrite Z.pow_add_r by lia.
  pose proof (Z.pow_pos_nonneg 2 s ltac:(lia) Hs) as P2.
  split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_lt_mono_pos_r; lia].
Qed.

(** The 64-bit wrap the stepper leaves on a shift is the identity below [2 ^ 64]. *)
Lemma bnd_mod : forall x k, k <= 64 -> 0 <= x < 2 ^ k -> 0 <= x mod 2 ^ 64 < 2 ^ k.
Proof.
  intros x k Hk H. assert (2 ^ k <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
  rewrite Z.mod_small by lia. exact H.
Qed.

(** [bnd_mod] with the modulus as the literal the stepper folds it to. *)
Lemma bnd_modl : forall x k, k <= 64 -> 0 <= x < 2 ^ k -> 0 <= x mod 18446744073709551616 < 2 ^ k.
Proof. intros x k Hk H. change 18446744073709551616 with (2 ^ 64). apply bnd_mod; assumption. Qed.

(** Proves [0 <= v < 2 ^ k] for a value built from read bytes by [Z.lor], [Z.shiftl] by a literal
    and the 64-bit wrap (the fuzz_u16 / fuzz_u32 assembly), from the [Hb] ranges of the bytes; any
    other goal goes to lia. *)
Ltac bnd :=
  lazymatch goal with
  | |- 0 <= Z.lor _ _ < 2 ^ _ => apply lor_lt_pow; [lia | bnd | bnd]
  | |- 0 <= Z.shiftl ?x ?s < 2 ^ ?k =>
      let j := eval vm_compute in (k - s) in apply (bnd_shl x s k j); [lia | reflexivity | bnd]
  | |- 0 <= _ mod 18446744073709551616 < 2 ^ _ => apply bnd_modl; [lia | bnd]
  | |- 0 <= _ mod 2 ^ 64 < 2 ^ _ => apply bnd_mod; [lia | bnd]
  | |- _ => lia
  end.

(** ---- the record a reader fills ---- *)

(** The record with its four scalar fields a, b, c and delta replaced: a reader that stores some of
    them leaves the others at the record's values. [k_head kind i] is [kfl (k_head kind i) 0 0 0 0]
    by conversion. *)
Definition kfl (k : kcall) (a b c delta : Z) : kcall :=
  mkKcall (k_kind k) (k_pad k) (k_p k) (k_desk k) a b c delta (k_bytes k) (k_n k) (k_rc k)
          (k_before k) (k_out k) (k_want_rc k) (k_want k) (k_want_len k) (k_want_key k) (k_want_display k).

(** The record with a and b replaced, the fields a reader of two u32 values sets. *)
Definition kab (k : kcall) (a b : Z) : kcall := kfl k a b (k_c k) (k_delta k).

(** Every a and b a u32 read can produce give a record run() accepts. *)
Definition kw (k : kcall) : Prop :=
  forall a b, 0 <= a < 2 ^ 32 -> 0 <= b < 2 ^ 32 -> rec_wf (kab k a b).

(** [reader_ok] with the head's zero bytes and n: only the ranges of the four scalars remain. *)
Lemma reader_ok_zero : forall kind a b c delta,
  0 <= a < 2 ^ 32 -> 0 <= b < 2 ^ 32 -> 0 <= c < 2 ^ 32 -> - 2 ^ 31 <= delta < 2 ^ 31 ->
  (kind = 5 -> b < 2 ^ 16) -> (kind = 10 -> b < 256) -> (kind = 11 -> a < 256 /\ b < 256) ->
  reader_ok kind a b c delta (zb (repeat (b8 0) 24)) 0.
Proof.
  intros kind a b c delta Ha Hb Hc Hd H5 H10 H11.
  assert (EB : zb (repeat (b8 0) 24) = repeat 0 24) by (vm_compute; reflexivity).
  unfold reader_ok. rewrite EB, repeat_length.
  split; [exact Ha|]. split; [exact Hb|]. split; [exact Hc|]. split; [exact Hd|]. split; [reflexivity|].
  split; [apply Forall_forall; intros x Hx; apply repeat_spec in Hx; lia|].
  split; [lia|]. split; [exact H5|]. split; [exact H10 | exact H11].
Qed.

(** The head's record with the four scalars a reader stored is one run() accepts, for any kind of
    the switch, when the scalars satisfy [reader_ok]. *)
Lemma rec_wf_head : forall kind i a b c delta, 0 <= kind <= 11 -> 0 <= i <= 2 ->
  reader_ok kind a b c delta (zb (repeat (b8 0) 24)) 0 ->
  rec_wf (kfl (k_head kind i) a b c delta).
Proof.
  intros kind i a b c delta HK HI HR.
  unfold rec_wf, kfl, k_head.
  cbn [k_kind k_pad k_p k_desk k_a k_b k_c k_delta k_bytes k_n k_rc k_before k_out k_want_rc k_want
       k_want_len k_want_key k_want_display].
  split; [lia|].
  split.
  { unfold desk_at. cbn [k_p k_desk].
    assert (EI : i = 0 \/ i = 1 \/ i = 2) by lia.
    destruct EI as [-> | [-> | ->]]; unfold pers_of, sdesk; cbn.
    - left. split; reflexivity.
    - right. left. split; reflexivity.
    - right. right. split; reflexivity. }
  do 7 (split; [reflexivity|]).
  exact HR.
Qed.

(** [kw] for the head's record of a kind with no bound of its own on a or b. *)
Lemma kw_head : forall kind i, 0 <= kind <= 11 -> kind <> 5 -> kind <> 10 -> kind <> 11 -> 0 <= i <= 2 ->
  kw (k_head kind i).
Proof.
  intros kind i HK H5 H10 H11 HI a b Ha Hb.
  exact (rec_wf_head kind i a b 0 0 HK HI
           (reader_ok_zero kind a b 0 0 Ha Hb ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))).
Qed.

(** The record well-formed for every u32 b, with a, c and delta already stored: what the shared
    b-reading tail of FADER / STRIP_LEDS and METER needs. *)
Definition kwb (k : kcall) (x z w : Z) : Prop :=
  forall y, 0 <= y < 2 ^ 32 -> rec_wf (kfl k x y z w).

(** ---- the machine state at a reader cut ---- *)

(** The machine state at a cut inside a reader: the loop's invariant registers fixed, a0-a7, s5 and
    s7 free (pass the live ones as terms), the pc a literal. *)
Definition rd_st (E : cenv) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' : word)
    (ops pcv : Z) (m1 : word -> option byte) : machine_state :=
  MS (mkR ra' (Z_to_bv 64 (bv_unsigned (c_sp E) + -416)) (c_gp E) (c_tp E) t0' t1' t2'
          (Z_to_bv 64 (bv_unsigned (c_sp E) + -308)) (Z_to_bv 64 0x1f678)
          a0' a1' a2' a3' a4' a5' a6' a7'
          (Z_to_bv 64 0x104d4) (Z_to_bv 64 254) (Z_to_bv 64 18446744073709422983)
          s5' (Z_to_bv 64 ops) s7' (Z_to_bv 64 (bv_unsigned (c_sp E) + -216)) (Z_to_bv 64 1)
          (Z_to_bv 64 18446744073709484843) (Z_to_bv 64 10) t3' t4' t5' t6')
     (c_F E) (Z_to_bv 64 pcv) (c_fc E) None m1 (seg_rom rsegs).

(** ---- handing the record to run() ---- *)

(** The end of a reader: any record [k] that run() accepts, in the frame with the cursor
    [Z_to_bv 64 cz] and in.n [Z_to_bv 64 rz], at the pc [pcv] of a [rec_ok] the reader holds
    ([RUN k] of [rd_run] for 0x14390, of [rd_run_arm] for a direct jump to an encoder arm). *)
Lemma rd_end : forall (E : cenv) (n : nat) (pcv : Z) (k : kcall) (cz rz ops : Z)
    (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' : word)
    (u0 pj tj plj : list byte) (m1 : word -> option byte),
  env_ok E ->
  (rec_wf k -> rec_ok E n k pcv) -> rec_wf k ->
  256 - ops <= Z.of_nat n -> 0 <= ops <= 255 ->
  bv_unsigned (c_p E) <= cz -> 0 <= rz -> cz - bv_unsigned (c_p E) + rz = Z.of_nat (length (c_data E)) ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -416) [CB 8 u0] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -408)
    [C8 (Z_to_bv 64 0x990); C8 (Z_to_bv 64 0x5cb0); C8 (Z_to_bv 64 0xffff)] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -384) (kcall_cells k) ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -200) [C8 (Z_to_bv 64 cz); C8 (Z_to_bv 64 rz)] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -184) [CB 5 pj] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -179) [CB 65 tj] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -114) [CB 10 plj] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -104) (saved E) ->
  stk rsegs m1 (c_lo E) (bv_unsigned (c_sp E) + -416) ->
  munch [(bv_unsigned (c_sp E) - 640, bv_unsigned (c_sp E))] (c_m E) m1 ->
  wmono rsegs (c_m E) m1 ->
  mem_inv rsegs m1 ->
  evt rsegs (Qk E) (rd_st E ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' ops pcv m1).
Proof.
  intros E n pcv k cz rz ops ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6'
    u0 pj tj plj m1 ENV RUN WF Ho1 Ho2 Hcz Hrz Hcr F0 F8 FK FIN FPD FTX FPL FSV ST MU WM HMI.
  pose proof ENV as (_ & _ & _ & _ & _ & _ & HPB & _ & _ & _).
  pose proof (bv_unsigned_in_range 64 (c_p E)) as Rp. unfold bv_modulus in Rp.
  pose proof (RUN WF) as R. unfold rec_ok in R.
  apply (R ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6'
           (Z_to_bv 64 cz) (Z_to_bv 64 rz) u0 pj tj plj (cz - bv_unsigned (c_p E)) ops m1);
    try assumption.
  - rewrite unsigned_lit by lia. lia.
  - lia.
  - rewrite unsigned_lit by lia. lia.
  - exact (conj (kcall_cells_size _) (conj F0 (conj F8 (conj FK (conj FIN (conj FPD (conj FTX (conj FPL FSV)))))))).
Qed.

(** ---- the shared steps of a reader proof ---- *)

(** The ranges a walk inside a reader needs, from [env_ok] and [stk] in the context: LO, HPB, HPNZ,
    Rsp, Rp, Hlo0. *)
Ltac rd_pre :=
  lazymatch goal with ENV : env_ok ?E |- _ =>
  let LO := fresh "LO" in let HPB := fresh "HPB" in let HPNZ := fresh "HPNZ" in
  pose proof ENV as (_ & _ & _ & LO & _ & _ & HPB & HPNZ & _ & _);
  let Rsp := fresh "Rsp" in let Rp := fresh "Rp" in
  pose proof (bv_unsigned_in_range 64 (c_sp E)) as Rsp; unfold bv_modulus in Rsp;
  pose proof (bv_unsigned_in_range 64 (c_p E)) as Rp; unfold bv_modulus in Rp;
  lazymatch goal with ST : stk _ _ _ _ |- _ => let Hlo0 := fresh "Hlo0" in pose proof ST as (Hlo0 & _ & _) end
  end.

(** After [rd_pre] and a [rem_cases] split: [HP0 : 0 < bv_unsigned (c_p E)] when the context shows
    the input is not empty (what refutes the pointer-overflow trap edges), and env_ok's implication
    cleared so lia does not split on it. *)
Ltac rd_p0 :=
  lazymatch goal with HPNZ : 0 < _ -> 0 < bv_unsigned (c_p ?E) |- _ =>
    try (let HP0 := fresh "HP0" in assert (HP0 : 0 < bv_unsigned (c_p E)) by (apply HPNZ; lia));
    clear HPNZ
  end.

(** The record hypothesis as the explicit cell list the loader and the stores need. *)
Ltac rd_unfold_k FK :=
  unfold kcall_cells in FK; try unfold kab in FK; try unfold kfl in FK; try unfold k_head in FK;
  cbn [k_kind k_pad k_p k_desk k_a k_b k_c k_delta k_bytes k_n k_rc k_before k_out k_want_rc k_want
       k_want_len k_want_key k_want_display] in FK.

(** At the end of a path: read a, b, c, delta and the cursor off the frame and apply [rd_end] with
    the record [kfl k a b c delta] and the [rec_ok] [RUN _]. Leaves the record's [rec_wf] and the
    frame facts (close them with [first [ <rec_wf proof> | eassumption | bnd ]]). *)
Ltac rd_to_run k RUN :=
  lazymatch goal with
  | ENV : env_ok ?E,
    FK : rw_cells _ _ (bv_unsigned (c_sp ?E) + -384)
           (_ :: _ :: _ :: _ :: C4 (Z_to_bv 64 ?A) :: C4 (Z_to_bv 64 ?B) :: C4 (Z_to_bv 64 ?C)
              :: C4 (Z_to_bv 64 ?D) :: _),
    FIN : rw_cells _ _ (bv_unsigned (c_sp ?E) + -200) [C8 (Z_to_bv 64 ?CZ); C8 (Z_to_bv 64 ?RZ)] |- _ =>
      eapply (rd_end E _ _ (kfl k A B C D) CZ RZ); [ exact ENV | exact (RUN _) | .. ]
  end.

(** ---- the tail RD0/7+6: b = fuzz_u32, shared by FADER / STRIP_LEDS and METER ---- *)

Section RDTAIL.
Variable E : cenv.
Variable n : nat.
Hypothesis ENV : env_ok E.
Hypothesis RUN : rd_run E n.

(** 0x14370-0x1438c: in.n was 0 when the b read started (a0 = 0), so b = 0; to run()'s switch. *)
Lemma rd_tail_zero : forall (k : kcall) (x z w cz rz ops : Z)
    (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' : word)
    (u0 pj tj plj : list byte) (m1 : word -> option byte),
  kwb k x z w -> bv_unsigned a0' = 0 ->
  256 - ops <= Z.of_nat n -> 0 <= ops <= 255 ->
  bv_unsigned (c_p E) <= cz -> 0 <= rz -> cz - bv_unsigned (c_p E) + rz = Z.of_nat (length (c_data E)) ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -416) [CB 8 u0] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -408)
    [C8 (Z_to_bv 64 0x990); C8 (Z_to_bv 64 0x5cb0); C8 (Z_to_bv 64 0xffff)] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -384) (kcall_cells (kfl k x 0 z w)) ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -200) [C8 (Z_to_bv 64 cz); C8 (Z_to_bv 64 rz)] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -184) [CB 5 pj] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -179) [CB 65 tj] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -114) [CB 10 plj] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -104) (saved E) ->
  stk rsegs m1 (c_lo E) (bv_unsigned (c_sp E) + -416) ->
  munch [(bv_unsigned (c_sp E) - 640, bv_unsigned (c_sp E))] (c_m E) m1 ->
  wmono rsegs (c_m E) m1 ->
  mem_inv rsegs m1 ->
  evt rsegs (Qk E) (rd_st E ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6'
                          ops 0x14370 m1).
Proof.
  intros k x z w cz rz ops ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' u0 pj tj plj m1
    KWB HA0 Ho1 Ho2 Hcz Hrz Hcr F0 F8 FK FIN FPD FTX FPL FSV ST MU WM HMI.
  rewrite <- (Z_to_bv_lit_self a0'), HA0.
  rd_pre. unfold rd_st. rd_unfold_k FK.
  drive 0x14390.
  rd_to_run k RUN.
  all: first [ apply KWB; bnd | eassumption | bnd ].
Qed.

(** 0x13c4c-0x13cdc, 0x1437c-0x1438c: b = fuzz_u32 with in.n = rz >= 1 in a0; to run()'s switch. *)
Lemma rd_tail_go : forall (k : kcall) (x z w cz rz ops : Z)
    (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' : word)
    (u0 pj tj plj : list byte) (m1 : word -> option byte),
  kwb k x z w -> 1 <= rz ->
  256 - ops <= Z.of_nat n -> 0 <= ops <= 255 ->
  bv_unsigned (c_p E) <= cz -> 0 <= rz -> cz - bv_unsigned (c_p E) + rz = Z.of_nat (length (c_data E)) ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -416) [CB 8 u0] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -408)
    [C8 (Z_to_bv 64 0x990); C8 (Z_to_bv 64 0x5cb0); C8 (Z_to_bv 64 0xffff)] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -384) (kcall_cells (kfl k x 0 z w)) ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -200) [C8 (Z_to_bv 64 cz); C8 (Z_to_bv 64 rz)] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -184) [CB 5 pj] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -179) [CB 65 tj] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -114) [CB 10 plj] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -104) (saved E) ->
  stk rsegs m1 (c_lo E) (bv_unsigned (c_sp E) + -416) ->
  munch [(bv_unsigned (c_sp E) - 640, bv_unsigned (c_sp E))] (c_m E) m1 ->
  wmono rsegs (c_m E) m1 ->
  mem_inv rsegs m1 ->
  evt rsegs (Qk E) (rd_st E ra' t0' t1' t2' (Z_to_bv 64 rz) a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6'
                          ops 0x13c4c m1).
Proof.
  intros k x z w cz rz ops ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' u0 pj tj plj m1
    KWB H1 Ho1 Ho2 Hcz Hrz Hcr F0 F8 FK FIN FPD FTX FPL FSV ST MU WM HMI.
  rd_pre. unfold rd_st. rd_unfold_k FK.
  destruct (rem_cases rz Hrz) as [R | [R | [R | [R | R]]]]; [exfalso; lia | ..]; try subst rz.
  all: rd_p0.
  all: drive 0x14390.
  all: rd_to_run k RUN.
  all: first [ apply KWB; bnd | eassumption | bnd ].
Qed.

End RDTAIL.

(** The b read of the shared tail from a reader's branch on in.n (0x13c48 for FADER / STRIP_LEDS,
    0x1436c for METER), the goal at 0x13c4c or 0x14370 and the record hypothesis unfolded: a, c,
    delta and the cursor read off the frame. Leaves only the record's [kwb] goal. *)
Ltac rd_to_tail E n ENV RUN k :=
  lazymatch goal with
  | FK : rw_cells _ _ (bv_unsigned (c_sp E) + -384)
           (_ :: _ :: _ :: _ :: C4 (Z_to_bv 64 ?X) :: _ :: C4 (Z_to_bv 64 ?Z) :: C4 (Z_to_bv 64 ?W) :: _),
    FIN : rw_cells _ _ (bv_unsigned (c_sp E) + -200) [C8 (Z_to_bv 64 ?CZ); C8 (Z_to_bv 64 ?RZ)] |- ?G =>
    lazymatch G with
    | evt _ _ (MS _ _ (Z_to_bv 64 0x13c4c) _ _ _ _) => eapply (rd_tail_go E n ENV RUN k X Z W CZ RZ)
    | evt _ _ (MS _ _ (Z_to_bv 64 0x14370) _ _ _ _) => eapply (rd_tail_zero E n ENV RUN k X Z W CZ RZ)
    end;
    try first [ eassumption | (rewrite unsigned_lit by lia; lia) | bnd ]
  end.
