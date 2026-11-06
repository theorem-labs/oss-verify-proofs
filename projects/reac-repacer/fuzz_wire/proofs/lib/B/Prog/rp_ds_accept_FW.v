(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_wire/lib/B/Prog/is_tagged_reac_F.v, with its module names changed; 228 of its 288 lines of code are new or changed and 132 lines of the source are left out. *)
(* rp_ds_accept_FW: the footprint walk of reac-repacer/fuzz_wire's rp_ds_accept in image B (fuzz_wire.asan-ubsan).
   rp_ds_accept_holds_F proves the frozen lib/B/Prog/rp_ds_accept_cg.v wire_rp_ds_accept_holds_stmt: is_tagged_reac's
   footprint contract (lib/B/Prog/is_tagged_reac_F_c.v) implies rp_ds_accept's (lib/B/Prog/rp_ds_accept_F_c.v).
   The stepping is lib/U/Prog/rp_ds_accept.v's (the UBSan walk: the split on n < 18, the null trap stepped over from
   `bv_unsigned a0 <> 0`, the tail jump to is_tagged_reac taken through that function's contract). The footprint form
   (StepF's step, one rng fact per access, the frame carved and released, the shadow base through its GOT word, the
   shadow loads read from the `addressable` premise, one check lemma per shadow test) is reac-repacer/fuzz_uci's
   lib/B/Prog/rp_hot_clamp_FW.v (recipes commit 0295462466b2) for one-byte loads. The chained form
   `<callee>_contract_F -> <fn>_contract_F`, the cut at the callee's entry and the composition of the two posts are
   libreac/fuzz_decode's lib/B/Prog/reac_decode_F.v reac_decode_holds_F (recipes commit 48907dc7e8ca); the cell
   transport is that commit's lib/B/Prog/ReacDecodeLib.v asan_cells_munch, restated at this unit's rows
   (lib/B/AsanCells.v). *)
(* rp_ds_accept of fuzz_wire.asan-ubsan (objdump of record sha256 440b9550f4f5; entry 0x80f84, 0xb8 bytes):
     0x80f84 `addi sp, sp, -16`, 0x80f88 `sd ra, 8(sp)` (its only store);
     0x80f8c `li a2, 18`, 0x80f90 `bgeu a1, a2, 0x80fa4`: n < 18 falls to 0x80f94 `li a0, 0`, 0x80f98 `ld ra, 8(sp)`,
       0x80f9c `addi sp, sp, 16`, 0x80fa0 `ret`;
     0x80fa4 `beqz a0, 0x81018`, 0x80fa8 `li a1, -12`, 0x80fac `bgeu a0, a1, 0x81018` (UBSan; `unimp` at 0x81018):
       a0 <> 0 and f + 18 <= APPMEM_END make both fall through;
     0x80fb0 `auipc a1, 0x18`, 0x80fb4 `ld a1, -1848(a1)` (the GOT word 0x98878), 0x80fb8 `ld a2, 0(a1)` (the shadow
       base in 0xa07f8);
     0x80fbc .. 0x80fcc: the shadow byte of f + 12 into a3, `bnez a3, 0x8101c`; 0x8101c `andi a4, a1, 7`, 0x81020
       `blt a4, a3, 0x80fd0` returns (ck_80fcc), so the report call at 0x81028 is never reached;
     0x80fd0 `lbu a1, 0(a1)` (f[12]), 0x80fd4 `li a3, 136`, 0x80fd8 `bne a1, a3, 0x8100c`;
     0x80fdc `li a1, -14`, 0x80fe0 `bltu a1, a0, 0x81018` (UBSan): falls through as above;
     0x80fe4 .. 0x80ff4: the shadow byte of f + 13 into a2, `bnez a2, 0x8102c`; 0x8102c `andi a3, a1, 7`, 0x81030
       `blt a3, a2, 0x80ff8` returns (ck_80ff4), so the report call at 0x81038 is never reached;
     0x80ff8 `lbu a1, 0(a1)` (f[13]), 0x80ffc `li a2, 25`, 0x81000 `bne a1, a2, 0x8100c`;
     0x81004 `li a0, 1`, 0x81008 `j 0x80f98`: returns 1;
     0x8100c `ld ra, 8(sp)`, 0x81010 `addi sp, sp, 16`, 0x81014 `j 0x8103c`: the tail jump to is_tagged_reac, with ra,
       sp and a0 = f as at entry, a1 .. a4 changed, a5 .. t6 as at entry, and the memory after the store of ra
       (rda_tail). *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import AsanKA AsanKAProof.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import is_tagged_reac_F_c rp_ds_accept_F_c rp_ds_accept_cg.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF StepF.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_ds_accept_c rp_copy_untag_c.
Import ListNotations.
Open Scope Z_scope.
Module PDA := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_ds_accept_c.
Module PCU := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_copy_untag_c.
Module PIT := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.is_tagged_reac_F_c.

(* ---- helpers ---- *)

(* the one-byte window of the shadow range of [p, p + n) at the shadow byte of a *)
Lemma rda_shadow_one : forall RNG p n a,
  ExecF.rng RNG (shadow_addr p) (shadow_addr (p + n - 1) - shadow_addr p + 1) ->
  p <= a < p + n -> ExecF.rng RNG (shadow_addr a) 1.
Proof.
  intros RNG p n a H Ha. unfold shadow_addr in *.
  assert (L1 : p / 8 <= a / 8) by (apply Z.div_le_mono; lia).
  assert (L2 : a / 8 <= (p + n - 1) / 8) by (apply Z.div_le_mono; lia).
  eapply ExecF.rng_sub; [exact H | lia | lia].
Qed.

(* the shadow check of a one-byte access at X passes on shadow byte k *)
Definition rda_shok1 (k : byte) (X : Z) : Prop := bv_signed k = 0 \/ X mod 8 < bv_signed k.

Lemma rda_shok1_of : forall (k : byte) X, shadow_ok X (bv_signed k) -> rda_shok1 k X.
Proof. intros k X [C|[C _]]; [left | right]; exact C. Qed.

Lemma rda_nth_error_firstn : forall (A : Type) (l : list A) k i, (i < k)%nat ->
  nth_error (firstn k l) i = nth_error l i.
Proof.
  intros A l. induction l as [|x l IH]; intros k i Hi.
  - destruct k, i; reflexivity.
  - destruct k as [|k]; [lia|]. destruct i as [|i]; [reflexivity|]. cbn [firstn nth_error]. apply IH. lia.
Qed.

Lemma rda_nth_firstn : forall (A : Type) (l : list A) k i d, (i < k)%nat ->
  nth i (firstn k l) d = nth i l d.
Proof.
  intros A l. induction l as [|x l IH]; intros k i d Hi.
  - destruct k, i; reflexivity.
  - destruct k as [|k]; [lia|]. destruct i as [|i]; [reflexivity|]. cbn [firstn nth]. apply IH. lia.
Qed.

(* the first k bytes of a frame are at its address *)
Lemma rda_bytes_at_firstn : forall m a (bs : list byte) k, (k <= length bs)%nat ->
  bytes_at rsegs m a bs -> bytes_at rsegs m a (firstn k bs).
Proof.
  intros m a bs k Hk (H0 & H1 & H).
  split; [exact H0|]. rewrite length_firstn, Nat.min_l by exact Hk.
  split; [lia|].
  intros i Hi. rewrite rda_nth_error_firstn by exact Hi. apply H. lia.
Qed.

(* lib/B/AsanCells.v asan_cells (its 19 rows, every one inside [GOT_CELL_K, MIDEND + 8)) holds after a write that lies
   off that region (libreac/fuzz_decode's lib/B/Prog/ReacDecodeLib.v asan_cells_munch, at this unit's rows) *)
Lemma rda_asan_cells_munch : forall m m' lo hi, asan_cells m -> munch [(lo, hi)] m m' ->
  MIDEND + 8 <= lo \/ hi <= GOT_CELL_K -> asan_cells m'.
Proof.
  unfold asan_cells, MIDEND, GOT_CELL_K.
  intros m m' lo hi (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15 & C16 & C17 & C18
    & C19) MU D.
  unfold CELL_K, GOT_CELL_K, INITED, REPLACE, GOT_REPLACE, UAR, GOT_UAR, CANPOISON, HIEND, GOT_HIEND, MIDBEG,
    GOT_MIDBEG, MIDEND, GOT_MIDEND, REAL_MEMCPY, GOT_REAL_MEMCPY, REAL_MEMSET, GOT_REAL_MEMSET, REAL_BCMP in *.
  repeat (match goal with |- _ /\ _ => split end);
    (eapply bytes_tp; [exact MU | | eassumption]); rewrite ?length_le8, ?length_le4; cbn [length]; lia.
Qed.

(* addressable is kept by a write into a 16-byte frame of application memory: the shadow bytes of application memory
   are not application memory *)
Lemma rda_addressable_frame : forall m m' s p n, addressable m p n -> munch [(s - 16, s)] m m' ->
  app_mem (s - 16) -> app_mem (s - 1) -> addressable m' p n.
Proof.
  intros m m' s p n (H0 & H1 & H2 & H) MU A1 A2.
  split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hok).
  split; [exact Ha|]. exists b. split; [|exact Hok].
  unfold shadow_addr, ASAN_K in *.
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Ha, A1, A2.
  apply (mrd_tp m m' (s - 16) s); [exact MU | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia | exact Hb].
Qed.

Lemma rda_addressable_sub : forall m p n q k, addressable m p n -> p <= q -> q + k <= p + n -> 0 <= k ->
  addressable m q k.
Proof.
  intros m p n q k (H0 & H1 & H2 & H) Hq Hk Hk0.
  split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. replace (q + i) with (p + (q - p + i)) by lia. apply H. lia.
Qed.

(* when is_reac(f) fails (f[12] <> 0x88 or f[13] <> 0x19), rp_ds_accept's result past n >= 18 is is_tagged_reac's on
   the first 18 bytes *)
Lemma rda_tail_result : forall n bs, 18 <= n ->
  (PDA.ds_byte bs 12 <> 0x88 \/ PDA.ds_byte bs 13 <> 0x19) ->
  PIT.is_tagged_result (firstn 18 bs) = PDA.ds_accept_result n bs.
Proof.
  intros n bs Hn H.
  unfold PIT.is_tagged_result, PCU.cu_tagged, PCU.cu_byte, PDA.ds_accept_result, PDA.ds_byte in *.
  rewrite !rda_nth_firstn by lia.
  rewrite (proj2 (Z.ltb_ge n 18) Hn).
  destruct H as [H|H].
  - rewrite (proj2 (Z.eqb_neq _ _) H). reflexivity.
  - rewrite (proj2 (Z.eqb_neq _ _) H), andb_false_r. reflexivity.
Qed.

(* 0x8103c, reached by the tail jump at 0x81014 from either failed test (f[12] <> 0x88 at 0x80fd8, f[13] <> 0x19 at
   0x81000): is_tagged_reac's footprint contract taken at the memory m0 after the store of ra, on the first 18 frame
   bytes (the store may cover bytes of bs past f + 18), with each premise read off rp_ds_accept's; its post composed
   with the store's (munch over the same frame, wmono, stk). *)
Lemma rda_tail : forall (RNG : ExecF.footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 n r1 r2 r3 r4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m m0 : word -> option byte) (bs : list byte) (lo : Z),
  PIT.is_tagged_reac_contract_F ->
  18 <= bv_unsigned n ->
  (PDA.ds_byte bs 12 <> 0x88 \/ PDA.ds_byte bs 13 <> 0x19) ->
  bv_unsigned a0 <> 0 ->
  (18 <= length bs)%nat -> bytes_at rsegs m (bv_unsigned a0) bs ->
  off_stk sp 16 (bv_unsigned a0) 18 ->
  app_mem (bv_unsigned sp - 16) -> app_mem (bv_unsigned sp - 1) ->
  asan_cells m ->
  off_stk sp 16 GOT_CELL_K (MIDEND + 8 - GOT_CELL_K) ->
  addressable m (bv_unsigned a0 + 12) 6 ->
  ExecF.rng RNG (bv_unsigned sp - 16) 16 ->
  ExecF.rng RNG GOT_CELL_K 8 -> ExecF.rng RNG CELL_K 8 ->
  ExecF.rng RNG (bv_unsigned a0 + 12) 6 ->
  ExecF.rng RNG (shadow_addr (bv_unsigned a0 + 12))
    (shadow_addr (bv_unsigned a0 + 12 + 6 - 1) - shadow_addr (bv_unsigned a0 + 12) + 1) ->
  munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m0 -> wmono rsegs m m0 ->
  stk rsegs m0 lo (bv_unsigned sp) -> lo + 16 <= bv_unsigned sp ->
  ExecF.evtF rsegs RNG
    (fun ms' => exists (a1' a2' a3' a4' : word) (m' : word -> option byte),
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (PDA.ds_accept_result (bv_unsigned n) bs)) a1' a2' a3' a4'
                     a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (ret_pc ra) fc None m' (seg_rom rsegs) /\
       munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\
       wmono rsegs m m' /\
       stk rsegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 r1 r2 r3 r4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x8103c) fc None m0 (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 n r1 r2 r3 r4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m m0
    bs lo HI HL HT NZ LEN BA D0 APS1 APS2 CELLS DC ADR RFR RGC RCK RBUF RSH MU1 WM1 ST0 HLO.
  unfold PIT.is_tagged_reac_contract_F, PIT.IS_TAGGED_REAC, PIT.IS_TAGGED_REAC_FRAME in HI.
  pose proof (rda_addressable_frame m m0 (bv_unsigned sp) _ _ ADR MU1 APS1 APS2) as ADR0.
  eapply ExecF.evtF_cut.
  { eapply (HI RNG ra sp gp tp t0 t1 t2 s0 s1 a0 r1 r2 r3 r4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
              F fc m0 (firstn 18 bs) lo).
    - exact NZ.
    - rewrite length_firstn, Nat.min_l by exact LEN. lia.
    - eapply bytes_tp; [exact MU1 | | apply rda_bytes_at_firstn; [exact LEN | exact BA]].
      rewrite length_firstn, Nat.min_l by exact LEN. unfold off_stk in D0. lia.
    - exact ST0.
    - exact HLO.
    - exact D0.
    - exact APS1.
    - exact APS2.
    - eapply rda_asan_cells_munch; [exact CELLS | exact MU1 | unfold off_stk in DC; lia].
    - unfold off_stk in DC |- *. unfold GOT_CELL_K, MIDEND in DC |- *. lia.
    - unfold off_stk in DC |- *. unfold GOT_CELL_K, CELL_K, MIDEND in DC |- *. lia.
    - apply (rda_addressable_sub m0 (bv_unsigned a0 + 12) 6 _ _ ADR0); lia.
    - apply (rda_addressable_sub m0 (bv_unsigned a0 + 12) 6 _ _ ADR0); lia.
    - exact RFR.
    - exact RGC.
    - exact RCK.
    - apply (ExecF.rng_sub RNG _ _ _ _ RBUF); lia.
    - apply (ExecF.rng_sub RNG _ _ _ _ RBUF); lia.
    - apply (ExecF.rng_sub RNG _ _ _ _ RSH); unfold shadow_addr; Z.div_mod_to_equations; lia.
    - apply (ExecF.rng_sub RNG _ _ _ _ RSH); unfold shadow_addr; Z.div_mod_to_equations; lia. }
  intros ms' (a1' & a2' & a3' & a4' & m2 & -> & MU2 & WM2 & ST2).
  apply ExecF.evtF_done. cbv beta.
  rewrite (rda_tail_result (bv_unsigned n) bs HL HT).
  exists a1', a2', a3', a4', m2.
  split; [reflexivity|].
  split; [eapply munch_trans; [exact MU1 | exact MU2]|].
  split; [eapply wmono_trans; [exact WM1 | exact WM2]|].
  exact ST2.
Qed.

(* ---- tactics ---- *)

Local Ltac zc H := zify_cond H; rewrite ?zxb_u in H.

(* lib/U/Prog/rp_ds_accept.v bfacts *)
Local Ltac bfacts :=
  repeat match goal with
  | H : ?x = ?c |- context [Z.eqb ?x ?c] => rewrite (proj2 (Z.eqb_eq x c) H)
  | H : ?x <> ?c |- context [Z.eqb ?x ?c] => rewrite (proj2 (Z.eqb_neq x c) H)
  | H : ?x < ?c |- context [Z.ltb ?x ?c] => rewrite (proj2 (Z.ltb_lt x c) H)
  | H : ?c <= ?x |- context [Z.ltb ?x ?c] => rewrite (proj2 (Z.ltb_ge x c) H)
  end.

(* the shadow check from its `bnez` back to the access: k = 0 falls through, else `andi`; `blt` returns *)
Local Ltac chk1 HX C K :=
  unfold rda_shok1 in C;
  lazymatch type of C with bv_signed ?k = 0 \/ _ =>
  lazymatch type of HX with bv_unsigned _ = ?X =>
    let MB := fresh "MB" in
    pose proof (Z.mod_pos_bound X 8 ltac:(lia)) as MB;
    step; rewrite sxb_eq0; destruct C as [C|C];
    [ rewrite (proj2 (Z.eqb_eq _ _) C); cbn [negb]; apply K
    | rewrite (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb];
      step; step;
      rewrite land7, HX, (lts_low (X mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); apply K ]
  end end.

Section Checks.
Variables (RNG : footprint) (Q : machine_state -> Prop)
  (ra sp1 gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32).

(* the states of the walk: sp1 is the frame's sp; r0 .. r4 are a0 .. a4 (rp_ds_accept writes no other register) *)
Local Abbreviation ST pc m r0 r1 r2 r3 r4 :=
  (MS (mkR ra sp1 gp tp t0 t1 t2 s0 s1 r0 r1 r2 r3 r4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

(* 0x80fcc: `bnez a3` on the shadow byte of f + 12 (in a1); its check (`andi a4, a1, 7`; `blt a4, a3`) returns to
   0x80fd0: the `jal __asan_report_load1` at 0x81028 is not reached. *)
Lemma ck_80fcc : forall m (r0 r1 r2 r4 : word) (k : byte) X,
  bv_unsigned r1 = X -> rda_shok1 k X ->
  (forall v : word, evtF rsegs RNG Q (ST 0x80fd0 m r0 r1 r2 (sxb k) v)) ->
  evtF rsegs RNG Q (ST 0x80fcc m r0 r1 r2 (sxb k) r4).
Proof. intros m r0 r1 r2 r4 k X HX C K. chk1 HX C K. Qed.

(* 0x80ff4: `bnez a2` on the shadow byte of f + 13 (in a1); its check (`andi a3, a1, 7`; `blt a3, a2`) returns to
   0x80ff8: the `jal __asan_report_load1` at 0x81038 is not reached. *)
Lemma ck_80ff4 : forall m (r0 r1 r3 r4 : word) (k : byte) X,
  bv_unsigned r1 = X -> rda_shok1 k X ->
  (forall v : word, evtF rsegs RNG Q (ST 0x80ff8 m r0 r1 (sxb k) v r4)) ->
  evtF rsegs RNG Q (ST 0x80ff4 m r0 r1 (sxb k) r3 r4).
Proof. intros m r0 r1 r3 r4 k X HX C K. chk1 HX C K. Qed.

End Checks.

(* ---- the contract ---- *)

(* a return of rp_ds_accept itself: the model evaluated on the branch facts of the path, the post's registers and the
   frame released *)
Local Ltac fin :=
  apply ExecF.evtF_done; unfold PDA.ds_accept_result, PDA.ds_byte;
  repeat match goal with Eb : ?b = nth ?i ?l ?d |- context [nth ?i ?l ?d] => rewrite <- Eb end;
  try match goal with |- context [Z.ltb ?x 18] =>
        first [ rewrite (proj2 (Z.ltb_lt x 18)) by lia | rewrite (proj2 (Z.ltb_ge x 18)) by lia ] end;
  bfacts;
  do 5 eexists; split; [reflexivity|]; split; [eassumption|]; split; [eassumption|];
  lazymatch goal with FR : rw_cells _ _ _ _, ST : stk _ _ _ _ |- stk _ _ _ (bv_unsigned ?s) =>
    release_frame FR ST (bv_unsigned s); exact ST end.

Theorem rp_ds_accept_holds_F : wire_rp_ds_accept_holds_stmt.
Proof.
  unfold wire_rp_ds_accept_holds_stmt. intros HI.
  unfold rp_ds_accept_contract_F, RP_DS_ACCEPT, RP_DS_ACCEPT_FRAME.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs lo
    ST HLO HB RFR HR.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2^64) in Rsp.
  pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0. change (2 ^ Z.of_N 64) with (2^64) in Ra0.
  carve_frame 16%nat ST.
  (* addi sp, sp, -16; sd ra, 8(sp); li a2, 18; bgeu a1, a2 *)
  step. step. step. step. if_cases HL.
  2:{ (* n < 18: li a0, 0; ld ra; addi sp; ret *)
      zc HL. do 4 step. fin. }
  zc HL.
  destruct (HB ltac:(lia)) as (NZ & LEN & BA & D0 & APS1 & APS2 & CELLS & DC & ADR).
  destruct (HR ltac:(lia)) as (RGC & RCK & RBUF & RSH).
  clear HB HR.
  match goal with MU' : munch _ m ?m1 |- _ => rename MU' into MU1; rename m1 into m0 end.
  (* the cells in the memory after the store of ra: the frame lies off the whole cell region *)
  pose proof (rda_asan_cells_munch m m0 _ _ CELLS MU1 ltac:(unfold off_stk in DC; lia)) as CELLS0.
  pose proof CELLS0 as (CK & GCK & _).
  (* the two bytes it reads, f + 12 and f + 13: each is application memory and its shadow byte passes *)
  pose proof ADR as (P0 & N0 & PE & AB).
  destruct (AB 0 ltac:(lia)) as (APP12 & k12 & MK12 & SK12).
  destruct (AB 1 ltac:(lia)) as (APP13 & k13 & MK13 & SK13).
  clear AB.
  rewrite Z.add_0_r in APP12, MK12, SK12.
  replace (bv_unsigned a0 + 12 + 1) with (bv_unsigned a0 + 13) in APP13, MK13, SK13 by lia.
  apply rda_shok1_of in SK12, SK13.
  pose proof (rda_shadow_one RNG _ 6 (bv_unsigned a0 + 12) RSH ltac:(lia)) as RS12.
  pose proof (rda_shadow_one RNG _ 6 (bv_unsigned a0 + 13) RSH ltac:(lia)) as RS13.
  unfold off_stk, GOT_CELL_K, CELL_K, shadow_addr, ASAN_K in *.
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in APP12, APP13, APS1, APS2, PE.
  (* the GOT word and the shadow base, read in the memory after the store of ra *)
  assert (RDG : ov_read_bytes rsegs m0 (wa 624760) 8 = Some (le8 (wa 657400))).
  { replace (wa 624760) with (wa (624760 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m0 624760 _ 0 8 GCK ltac:(lia)) by (rewrite length_le8; lia). reflexivity. }
  assert (RDS : ov_read_bytes rsegs m0 (wa 657400) 8 = Some (le8 (wa 2147450880))).
  { replace (wa 657400) with (wa (657400 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m0 657400 _ 0 8 CK ltac:(lia)) by (rewrite length_le8; lia). reflexivity. }
  pose proof (mrd_tp m m0 _ _ ((bv_unsigned a0 + 12) / 8 + 2147450880) _ MU1
    ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia) MK12) as M12.
  pose proof (mrd_tp m m0 _ _ ((bv_unsigned a0 + 13) / 8 + 2147450880) _ MU1
    ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia) MK13) as M13.
  pose proof (mrd_tp m m0 _ _ (bv_unsigned a0 + Z.of_nat 12) _ MU1 ltac:(lia) ltac:(lia)
    (bytes_nth m _ bs 12 BA ltac:(lia))) as F12.
  pose proof (mrd_tp m m0 _ _ (bv_unsigned a0 + Z.of_nat 13) _ MU1 ltac:(lia) ltac:(lia)
    (bytes_nth m _ bs 13 BA ltac:(lia))) as F13.
  change (Z.of_nat 12) with 12 in F12. change (Z.of_nat 13) with 13 in F13.
  remember (nth 12 bs (Z_to_bv 8 0)) as b12 eqn:E12.
  remember (nth 13 bs (Z_to_bv 8 0)) as b13 eqn:E13.
  (* the UBSan checks of f: `beqz a0` and `bgeu a0, a1` (a1 = -12) fall through *)
  step. if_false.
  step. step. if_false.
  (* the shadow base through its GOT word *)
  step. step. step.
  (* f + 12: its shadow byte and check *)
  step. gen_addi a0 w12 U12.
  assert (RW12 : ExecF.rng RNG (bv_unsigned w12) 1) by (apply (ExecF.rng_sub RNG _ _ _ _ RBUF); lia).
  step. gen_shr w12 g12 G12. rewrite U12 in G12.
  step. gen_addi g12 h12 H12.
  assert (RH12 : ExecF.rng RNG (bv_unsigned h12) 1) by (apply (ExecF.rng_sub RNG _ _ _ _ RS12); lia).
  pose proof (rdw0 m0 h12 _ _ M12 ltac:(lia)) as R. step. clear R.
  eapply ck_80fcc with (X := bv_unsigned a0 + 12); [exact U12 | exact SK12 | intros v12].
  (* f[12]; li a3, 136; bne a1, a3 *)
  pose proof (rdw0 m0 w12 _ _ F12 ltac:(lia)) as R. step. clear R.
  step. step. if_cases HC12; zc HC12.
  { (* f[12] <> 0x88: ld ra; addi sp; j is_tagged_reac *)
    do 3 step. release_frame FR ST (bv_unsigned sp).
    eapply rda_tail;
      [ exact HI | lia | left; unfold PDA.ds_byte; rewrite <- E12; lia | exact NZ | exact LEN | exact BA
      | exact D0 | exact APS1 | exact APS2 | exact CELLS | exact DC | exact ADR | exact RFR | exact RGC | exact RCK
      | exact RBUF | exact RSH | exact MU1 | eassumption | exact ST | lia ]. }
  (* the UBSan check `bltu a1, a0` (a1 = -14) falls through *)
  step. step. if_false.
  (* f + 13: its shadow byte and check *)
  step. gen_addi a0 w13 U13.
  assert (RW13 : ExecF.rng RNG (bv_unsigned w13) 1) by (apply (ExecF.rng_sub RNG _ _ _ _ RBUF); lia).
  step. gen_shr w13 g13 G13. rewrite U13 in G13.
  step. gen_addi g13 h13 H13.
  assert (RH13 : ExecF.rng RNG (bv_unsigned h13) 1) by (apply (ExecF.rng_sub RNG _ _ _ _ RS13); lia).
  pose proof (rdw0 m0 h13 _ _ M13 ltac:(lia)) as R. step. clear R.
  eapply ck_80ff4 with (X := bv_unsigned a0 + 13); [exact U13 | exact SK13 | intros v13].
  (* f[13]; li a2, 25; bne a1, a2 *)
  pose proof (rdw0 m0 w13 _ _ F13 ltac:(lia)) as R. step. clear R.
  step. step. if_cases HC13; zc HC13.
  { (* f[13] <> 0x19: ld ra; addi sp; j is_tagged_reac *)
    do 3 step. release_frame FR ST (bv_unsigned sp).
    eapply rda_tail;
      [ exact HI | lia | right; unfold PDA.ds_byte; rewrite <- E13; lia | exact NZ | exact LEN | exact BA
      | exact D0 | exact APS1 | exact APS2 | exact CELLS | exact DC | exact ADR | exact RFR | exact RGC | exact RCK
      | exact RBUF | exact RSH | exact MU1 | eassumption | exact ST | lia ]. }
  (* f[12] = 0x88 and f[13] = 0x19: li a0, 1; j; ld ra; addi sp; ret *)
  do 5 step. fin.
Qed.
