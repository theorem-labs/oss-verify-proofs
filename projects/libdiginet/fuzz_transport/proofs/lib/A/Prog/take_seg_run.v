(* take_seg_run: the footprint runs (lib/Lib/ExecF.v evtF, stepped with lib/Lib/StepF.v) of take in image A
   (fuzz_transport.asan, entry 0x8a508 = transport_sigma TS_take, 307 words; listing lib/A/Prog/DgnTransportList.v
   from AF_take = 0x92a4). The machine walk lib/A/Prog/take_cgW.v carries each of them into SRr with
   lib/A/Prog/DgnTransportCgRun.v decode_run and cuts the four calls (three of __asan_memcpy, one of
   diginet_body_check) between them.

   The cuts (offsets from the entry):
     +0x000  TK_ENTRY  the prologue, the 4-byte store of 0 at has_display, s->queued;
             queued <> 0 goes to the loop head, queued = 0 to the exit;
     +0x0fc  TK_L      the loop head of :358-382, turn i;
     +0x174  TK_CPY1   memcpy (body + len, c->bytes, c->len) (:365);
     +0x178  TK_R1     its return; then
     +0x184  TK_BCC    diginet_body_check (body, len + c->len) (:366);
     +0x188  TK_R2     its return: 0 takes the command (:368-371), anything else refuses;
     +0x218  TK_NF     the refusal (:373-375): kept = i skips the copy, else
     +0x244  TK_CPY2   memcpy (&s->queue[kept], c, 32) (:374), returning at
     +0x248  TK_R3;
     +0x26c  TK_J      the end of a turn (:377): the break test, then the next turn, the tail or the exit;
     +0x344  TK_BRK    the break (:378): the tail loop or the exit;
     +0x36c  TK_TL     the tail loop head, turn j;
     +0x380  TK_CPY3   memcpy (&s->queue[kept], &s->queue[j], 32), returning at
     +0x384  TK_R4;
     +0x3cc  TK_X      the exit (:383-385): s->queued = kept, *body_len = len, return taken.

   Every instrumented check reads one shadow byte. For an access of n < 8 bytes at a the code goes on when the byte
   is 0, else when (a & 7) + n - 1 < byte (signed); for the 8-byte store at body_len any nonzero byte is the error
   path. The reads inside g_s's payload have a zero shadow byte (the walk gets that from the record); the two cells
   of the caller's frame (has_display, body_len) carry the shadow byte as a hypothesis khd / kbl with the
   disjunction the check needs.

   No error path is reached: each of the 17 calls of __asan_report_* sits behind a test these hypotheses decide. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import
  PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA AsanKAProof TWorldG TWorldA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportSyms DgnTransportAddr.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TWorldLemmas TSess0 TTake.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.

(* ---- the addresses: the entry is the listing's name, every interior point an offset ---- *)

Definition TK_ENTRY : Z := transport_sigma TS_take.
Definition TK_AT (off : Z) : Z := TK_ENTRY + off.
Definition TK_L : Z := TK_AT 0xfc.
Definition TK_CPY1 : Z := TK_AT 0x174.
Definition TK_R1 : Z := TK_AT 0x178.
Definition TK_BCC : Z := TK_AT 0x184.
Definition TK_R2 : Z := TK_AT 0x188.
Definition TK_NF : Z := TK_AT 0x218.
Definition TK_CPY2 : Z := TK_AT 0x244.
Definition TK_R3 : Z := TK_AT 0x248.
Definition TK_J : Z := TK_AT 0x26c.
Definition TK_BRK : Z := TK_AT 0x344.
Definition TK_TL : Z := TK_AT 0x36c.
Definition TK_CPY3 : Z := TK_AT 0x380.
Definition TK_R4 : Z := TK_AT 0x384.
Definition TK_X : Z := TK_AT 0x3cc.
Definition TK_MEMCPY : Z := transport_sigma TS___asan_memcpy.
Definition TK_BC : Z := transport_sigma TS_diginet_body_check.

(* g_s's base in image A and the fields the code addresses. *)
Definition TK_S : Z := TA_g_s.
Definition TK_MAXC : Z := TK_S + 52.
Definition TK_MAXB : Z := TK_S + 56.
Definition TK_Q0 : Z := TK_S + 1760.
Definition TK_QD : Z := TK_S + 18144.
Definition TK_K : Z := ASAN_K.
Definition tk_sh (a : Z) : Z := a / 8 + TK_K.
Definition TK_FRAME : Z := 224.

Lemma tk_addrs : TK_ENTRY = 0x8a508 /\ TK_S = 0x5df9c0 /\ TK_MAXC = 0x5df9f4 /\ TK_MAXB = 0x5df9f8 /\
  TK_Q0 = 0x5e00a0 /\ TK_QD = 0x5e40a0 /\ TK_S mod 64 = 0 /\ TK_MEMCPY = 0x523b0 /\ TK_BC = 0x8c530.
Proof.
  repeat split; vm_compute; reflexivity.
Qed.

(* The 224-byte frame as 28 8-byte cells: offsets 0 .. 0xd8. Slots 0 .. 0x70 are the function's spills, slots
   0x78 .. 0xd8 the saved s11 .. s0 and ra. *)
Definition tk_fr (ws : list word) : list cell := map C8 ws.

(* The spills the prologue and the loop head leave, with the slot at 0x38 (the spill of taken, written only on the
   path through +0x154) free. *)
Definition tk_spill (bp blp hdp allow : Z) (j38 : word) : list word :=
  [Z_to_bv 64 3; Z_to_bv 64 7; Z_to_bv 64 hdp; Z_to_bv 64 (tk_sh hdp); Z_to_bv 64 TK_S; Z_to_bv 64 blp;
   Z_to_bv 64 bp; j38; Z_to_bv 64 allow; Z_to_bv 64 TK_Q0; Z_to_bv 64 (tk_sh TK_MAXB);
   Z_to_bv 64 (tk_sh TK_MAXC); Z_to_bv 64 TK_MAXB; Z_to_bv 64 TK_MAXC; Z_to_bv 64 TK_K].

Definition tk_saved (v11 v10 v9 v8 v7 v6 v5 v4 v3 v2 v1 v0 vra : word) : list word :=
  [v11; v10; v9; v8; v7; v6; v5; v4; v3; v2; v1; v0; vra].

(* ---- the proof kit of the runs ---- *)

(* Every address constant of the runs as its literal (StepF's step reads literal pcs; the arithmetic of the address
   registers folds on literals). *)
Ltac tk_lit c := let v := eval vm_compute in c in try change c with v in *.
Ltac tk_lits :=
  tk_lit TK_L; tk_lit TK_CPY1; tk_lit TK_R1; tk_lit TK_BCC; tk_lit TK_R2; tk_lit TK_NF; tk_lit TK_CPY2;
  tk_lit TK_R3; tk_lit TK_J; tk_lit TK_BRK; tk_lit TK_TL; tk_lit TK_CPY3; tk_lit TK_R4; tk_lit TK_X;
  tk_lit TK_MEMCPY; tk_lit TK_BC; tk_lit TK_ENTRY;
  tk_lit (tk_sh TK_MAXC); tk_lit (tk_sh TK_MAXB); tk_lit (tk_sh TK_QD);
  tk_lit TK_MAXC; tk_lit TK_MAXB; tk_lit TK_Q0; tk_lit TK_QD; tk_lit TK_S; tk_lit TK_FRAME;
  unfold tk_sh in *; tk_lit TK_K.

(* A branch decided to b. *)
Ltac tk_br b tac := lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b; [cbv iota | symmetry; tac]
  end.

(* The two machine states agree register by register (the arithmetic of a register by lia); the stepped state's
   registers are a TNode tree, so the post's mkR is unfolded too. *)
Ltac tk_tree :=
  first [ reflexivity
        | lazymatch goal with
          | |- TNode _ _ _ = TNode _ _ _ => f_equal; tk_tree
          | |- Some _ = Some _ => f_equal; tk_tree
          | |- Z_to_bv 64 _ = Z_to_bv 64 _ => f_equal; lia
          end ].
Ltac tk_ms :=
  cbv beta;
  lazymatch goal with
  | |- MS _ _ _ _ _ _ _ = MS _ _ _ _ _ _ _ => cbv delta [mkR]; f_equal; tk_tree
  end.

(* The end of a run: the post at the reached state, its existentials opened (w0 for a word the post ignores). *)
Ltac tk_exs :=
  repeat lazymatch goal with
         | |- @ex word (fun _ => ?P) => exists w0
         | |- @ex _ _ => eexists
         end.
Ltac tk_post := apply evtF_done; cbv beta; tk_exs.

(* A fact kept out of sight of StepF's load and store lookups. *)
Definition tk_hid (P : Prop) : Prop := P.
Lemma tk_hid_intro : forall P : Prop, P -> tk_hid P.
Proof. intros P H. exact H. Qed.

(* The carved frame as 8-byte cells: 8 bytes are the bytes of the word they read as, so a byte cell of 8 is a word
   cell, and 8 * n bytes are n word cells. *)
Lemma tk_le8_rt : forall bs, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs L. rewrite <- TWorldLemmas.put_le8.
  assert (E : bv_unsigned (le_bytes_to_word bs) = TW.u_at bs 0 8).
  { unfold TW.u_at. rewrite TWorldLemmas.sub_all by exact L. unfold le_bytes_to_word. rewrite Z_to_bv_unsigned.
    apply bv_wrap_small. pose proof (bytes_le_to_Z_bound bs) as B. pose proof (bytes_le_to_Z_nonneg bs) as N.
    rewrite L in B. change (8 * Z.of_nat 8) with 64 in B. change (bv_modulus 64) with (2 ^ 64). lia. }
  rewrite E, TTake.tk_put_u_at by (try rewrite L; lia). apply TWorldLemmas.sub_all. exact L.
Qed.

Lemma tk_cb8 : forall m A bs, rw_cells rsegs m A [CB 8 bs] -> rw_cells rsegs m A [C8 (le_bytes_to_word bs)].
Proof.
  intros m A bs H. pose proof (proj1 (proj1 (proj1 H))) as W. cbn [cells_wf cell_wf] in W.
  eapply TTake.tk_rebytes; [exact H | cbn; tauto |].
  cbn [cells_bytes cbytes]. rewrite !app_nil_r. apply tk_le8_rt. first [exact W | exact (proj1 W)].
Qed.

Lemma tk_c8s : forall n m A junk, rw_cells rsegs m A [CB (8 * n) junk] ->
  exists ws, length ws = n /\ rw_cells rsegs m A (map C8 ws).
Proof.
  induction n as [|n IH]; intros m A junk H.
  - exists []. split; [reflexivity|]. pose proof (rw_cells_bound rsegs m A _ H) as B.
    cbn [cells_size csize] in B. split; [split|].
    + exact I.
    + apply bytes_at_nil. lia.
    + split; [lia|]. split; [cbn; lia|]. intros k Hk. cbn in Hk. lia.
  - replace (8 * S n)%nat with (8 + 8 * n)%nat in H by lia.
    destruct (TTake.tk_cb_split m A 8 (8 * n) junk H) as [H1 H2].
    destruct (IH m (A + Z.of_nat 8) _ H2) as (ws & L & H3).
    exists (le_bytes_to_word (firstn 8 junk) :: ws). split; [cbn; rewrite L; reflexivity|].
    exact (TTake.tk_join2 m A (A + Z.of_nat 8) [C8 (le_bytes_to_word (firstn 8 junk))] (map C8 ws)
             (tk_cb8 m A _ H1) eq_refl H3).
Qed.

Lemma tk_len28 : forall (ws : list word), length ws = 28%nat ->
  exists w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27,
    ws = [w0; w1; w2; w3; w4; w5; w6; w7; w8; w9; w10; w11; w12; w13; w14; w15; w16; w17; w18; w19; w20; w21;
          w22; w23; w24; w25; w26; w27].
Proof.
  intros ws L.
  do 28 (destruct ws as [|? ws]; [discriminate L|]). destruct ws; [|discriminate L].
  do 28 eexists. reflexivity.
Qed.

(* The loads of a field's bytes put n v: lw gives s32_at, lwu and lbu the value itself. *)
Lemma tk_u_put4 : forall v, 0 <= v < 2 ^ 32 -> TW.u_at (TW.put 4 v) 0 4 = v.
Proof. intros v Hv. rewrite TWorldLemmas.u_at_put. apply Z.mod_small. exact Hv. Qed.

Lemma tk_s32_small : forall v, 0 <= v < 2 ^ 31 -> TW.s32_at (TW.put 4 v) 0 = v.
Proof. intros v Hv. unfold TW.s32_at. rewrite tk_u_put4 by lia. apply TTake.tk_swrap32_small. lia. Qed.

Lemma tk_lw_put : forall v,
  sext 64 (bv_extract 0 32 (le_bytes_to_word (TW.put 4 v))) = Z_to_bv 64 (TW.s32_at (TW.put 4 v) 0).
Proof.
  intros v. pose proof (lw_world (TW.put 4 v) 0) as H.
  rewrite TWorldLemmas.sub_all in H by apply TWorldLemmas.length_put. exact H.
Qed.

Lemma tk_lwu_put : forall v, 0 <= v < 2 ^ 32 ->
  zext 64 (bv_extract 0 32 (le_bytes_to_word (TW.put 4 v))) = Z_to_bv 64 v.
Proof.
  intros v Hv. pose proof (lwu_world (TW.put 4 v) 0) as H.
  rewrite TWorldLemmas.sub_all in H by apply TWorldLemmas.length_put. rewrite H, tk_u_put4 by exact Hv.
  reflexivity.
Qed.

Lemma tk_lbu_put : forall v, 0 <= v < 2 ^ 8 ->
  zext 64 (bv_extract 0 8 (le_bytes_to_word (TW.put 1 v))) = Z_to_bv 64 v.
Proof.
  intros v Hv. pose proof (lbu_world (TW.put 1 v) 0) as H.
  rewrite TWorldLemmas.sub_all in H by apply TWorldLemmas.length_put. rewrite H, TWorldLemmas.u_at_put.
  rewrite Z.mod_small by exact Hv. reflexivity.
Qed.

(* `srli rd,rs,3` of an address: the shadow index. *)
Lemma tk_shr3 : forall x, 0 <= x < 2 ^ 64 -> Z.shiftr (bv_unsigned (Z_to_bv 64 x)) 3 = x / 8.
Proof. intros x Hx. rewrite (unsigned_lit x) by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

(* A branch condition over register values, as a Z comparison decided by lia. *)
Ltac tk_zc :=
  lazymatch goal with
  | |- negb _ = false => apply Bool.negb_false_iff; tk_zc
  | |- negb _ = true => apply Bool.negb_true_iff; tk_zc
  | |- (_ <? _) = true => apply Z.ltb_lt; lia
  | |- (_ <? _) = false => apply Z.ltb_ge; lia
  | |- (_ =? _) = true => apply Z.eqb_eq; lia
  | |- (_ =? _) = false => apply Z.eqb_neq; lia
  end.
Ltac tk_cmp :=
  rewrite ?TTake.tk_eqb0 by lia;
  rewrite ?TTake.tk_ltu_s32, ?TTake.tk_eqb_s32 by lia;
  rewrite ?tk_u_put4 by lia;
  rewrite ?TTake.tk_ltu_lits, ?TTake.tk_eqb_lits by lia;
  tk_zc.

(* `slli rd,rs,5` of a small index: 32 times it. *)
Lemma tk_shl5 : forall k, 0 <= k < 2 ^ 58 -> Z.shiftl (bv_unsigned (Z_to_bv 64 k)) 5 = 32 * k.
Proof. intros k Hk. rewrite (unsigned_lit k) by lia. rewrite Z.shiftl_mul_pow2 by lia. lia. Qed.

(* `addiw rd,rs,c` of a small counter. *)
Lemma tk_addiw : forall x c, 0 <= x < 2 ^ 31 -> - 2 ^ 31 <= x + c < 2 ^ 31 ->
  bv_swrap 32 (bv_unsigned (Z_to_bv 64 x) + c) = x + c.
Proof. intros x c Hx Hxc. rewrite (unsigned_lit x) by lia. apply TTake.tk_swrap32_small. exact Hxc. Qed.

(* The signed reading of a small shadow byte. *)
Lemma tk_signed8 : forall k, -128 <= k < 128 -> bv_signed (Z_to_bv 8 k) = k.
Proof.
  intros k Hk. unfold bv_signed. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 8) with 256. change (256 / 2) with 128. Z.div_mod_to_equations. lia.
Qed.

(* The 13 saved words of the frame, one by one. *)
Lemma tk_len13 : forall (sv : list word), length sv = 13%nat ->
  exists v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12, sv = [v0; v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11; v12].
Proof.
  intros sv L.
  do 13 (destruct sv as [|? sv]; [discriminate L|]). destruct sv; [|discriminate L].
  do 13 eexists. reflexivity.
Qed.

Lemma tk_len15 : forall (ws : list word), length ws = 15%nat ->
  exists w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14,
    ws = [w0; w1; w2; w3; w4; w5; w6; w7; w8; w9; w10; w11; w12; w13; w14].
Proof.
  intros ws L.
  do 15 (destruct ws as [|? ws]; [discriminate L|]). destruct ws; [|discriminate L].
  do 15 eexists. reflexivity.
Qed.

(* The frame given back to the stack, whether or not the stack's low end lies below it. *)
Lemma tk_release : forall m lo A cs, stk rsegs m lo A -> rw_cells rsegs m A cs ->
  stk rsegs m lo (A + Z.of_nat (cells_size cs)).
Proof.
  intros m lo A cs ST FR. destruct (Z_le_gt_dec lo A) as [L|L].
  - exact (stk_release rsegs m lo A cs ST FR L).
  - pose proof (stk_of_rw_cells rsegs m A cs FR) as SA.
    destruct (Z_le_gt_dec lo (A + Z.of_nat (cells_size cs))) as [L2|L2].
    + exact (proj2 (stk_split rsegs m A lo _ SA ltac:(lia))).
    + destruct ST as (S1 & _ & _). destruct SA as (_ & S2 & _).
      split; [exact S1|]. split; [exact S2|]. intros a Ha. lia.
Qed.

(* A read of bytes off a run's written ranges W gives what it gave before the run. *)
Lemma tk_disj_succ : forall W a n, disjoint_from W a (Z.of_nat (S n)) -> disjoint_from W (a + 1) (Z.of_nat n).
Proof.
  induction W as [|[lo hi] W IH]; intros a n D; cbn in *; [exact I|].
  destruct D as [D1 D2]. split; [lia | apply IH; exact D2].
Qed.

Lemma tk_rd_mu : forall W (m m' : word -> option byte) (n : nat) a bs,
  munch W m m' -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> disjoint_from W a (Z.of_nat n) ->
  ov_read_bytes rsegs m (wa a) n = Some bs -> ov_read_bytes rsegs m' (wa a) n = Some bs.
Proof.
  intros W m m' n a bs MU Ha Hn D H. rewrite ov_rdn in H |- *. revert a bs Ha Hn D H.
  induction n as [|n IH]; intros a bs Ha Hn D H; rewrite rdn_unfold in H |- *; [exact H|].
  assert (E : mrd rsegs m' (wa a) = mrd rsegs m (wa a)).
  { unfold mrd. rewrite (MU (wa a)); [reflexivity|]. unfold wa. rewrite unsigned_lit by lia.
    apply (disjoint_outside W a (Z.of_nat (S n))); [exact D | lia]. }
  rewrite E. destruct (mrd rsegs m (wa a)) as [b|]; [|discriminate H].
  rewrite wa_succ in H |- *.
  destruct (rdn rsegs m (wa (a + 1)) n) as [r|] eqn:R; [|discriminate H].
  rewrite (IH (a + 1) r ltac:(lia) ltac:(lia) (tk_disj_succ W a n D) R). exact H.
Qed.

(* tk_rd_mu at the memory of the goal, from the munch fact MU of the run so far. *)
Ltac tk_disj := cbn [disjoint_from Z.of_nat Pos.of_succ_nat Pos.succ];
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Ltac tk_rd MU H :=
  lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      let H' := fresh H "'" in
      lazymatch type of H with
      | ov_read_bytes _ _ (wa ?a) ?n = Some ?bs => pose proof (tk_rd_mu _ _ mm n a bs MU) as H'
      | ov_read_bytes _ _ (Z_to_bv 64 ?a) ?n = Some ?bs => pose proof (tk_rd_mu _ _ mm n a bs MU) as H'
      end;
      specialize (H' ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) ltac:(tk_disj) H)
  end.

(* The prologue of take up to the test of has_display's shadow byte (+0x00 .. +0x60): the frame and the 15 stores
   of the saved registers, allow_display and body; the shadow base through its GOT word; the spill of the shadow
   byte address of has_display and its load. MF is the munch fact of the frame alone. *)
Local Ltac tk_pro MF RGC RCK RSH :=
  (* +0x00 addi sp,sp,-224; +0x04 .. +0x34 sd ra, s0 .. s11; +0x38 sd a3,0x40(sp); +0x3c sd a1,0x30(sp) *)
  do 16 step;
  (* +0x40 auipc a1; +0x44 ld a1: GOT_CELL_K; +0x48 ld a7,0(a1): the shadow base *)
  step; tk_rd MF RGC; step; tk_rd MF RCK; step;
  (* +0x4c srli a1,a4,3; +0x50 add a1,a1,a7; +0x54 sd a1,0x18(sp) *)
  step; rewrite tk_shr3 by lia; step; step;
  (* +0x58 lb a1,0(a1); +0x5c mv s7,a0; +0x60 bnez a1 *)
  tk_rd MF RSH; step; step; step.

(* The test of has_display's shadow byte khd: 0, or above hdp mod 8 + 3 (the slow path +0x430 .. +0x438). *)
Local Ltac tk_khd HK khd hdp :=
  destruct HK as [K0|[K1 K2]];
  [ subst khd; tk_br false ltac:(vm_compute; reflexivity)
  | tk_br true ltac:(rewrite sxb_eq0, tk_signed8 by lia; tk_zc);
    step; step; step;
    tk_br true ltac:(rewrite (unsigned_lit hdp), land7 by lia; rewrite lts_low by lia;
                     rewrite tk_signed8 by lia; tk_zc) ].

(* +0x64 .. +0x8c: *has_display = 0, &s->queued and its shadow byte address, the shadow check, the spill of
   body_len, the load of s->queued and its test. MU is the munch fact of the frame and has_display. *)
Local Ltac tk_pro2 MU RSQ RQ :=
  (* +0x64 sw zero,0(a4) *)
  step;
  (* +0x68 lui a0,4; +0x6c addiw s1,a0,0x6e0; +0x70 add s1,s7,s1; +0x74 srli a0,s1,3; +0x78 add s9,a0,a7 *)
  do 5 step;
  (* +0x7c lb a0,0(s9); +0x80 bnez a0 *)
  tk_rd MU RSQ; step; step; tk_br false ltac:(vm_compute; reflexivity);
  (* +0x84 sd a2,0x28(sp); +0x88 lw a0,0(s1): s->queued; +0x8c beqz a0 *)
  step; tk_rd MU RQ; step; rewrite tk_lw_put, tk_s32_small by lia; step.

(* ---- run 1: the prologue, s->queued <> 0, to the loop head ---- *)

Lemma tk_run_entry : forall (RNG : ExecF.footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (lo bp blp hdp allow khd queued : Z),
  (* the stack the prologue carves *)
  stk rsegs m lo (bv_unsigned sp) -> lo + TK_FRAME <= bv_unsigned sp ->
  ExecF.rng RNG (bv_unsigned sp - TK_FRAME) TK_FRAME ->
  (* the runtime cells: the GOT word of the shadow base and the cell it points at *)
  ov_read_bytes rsegs m (wa GOT_CELL_K) 8 = Some (le8 (wa CELL_K)) ->
  ov_read_bytes rsegs m (wa CELL_K) 8 = Some (le8 (wa ASAN_K)) ->
  ExecF.rng RNG GOT_CELL_K 8 -> ExecF.rng RNG CELL_K 8 ->
  (* the shadow byte of has_display, the shadow byte of s->queued (0: g_s's payload), and s->queued *)
  ov_read_bytes rsegs m (wa (tk_sh hdp)) 1 = Some [Z_to_bv 8 khd] ->
  ov_read_bytes rsegs m (wa (tk_sh TK_QD)) 1 = Some [Z_to_bv 8 0] ->
  ov_read_bytes rsegs m (wa TK_QD) 4 = Some (TW.put 4 queued) ->
  ExecF.rng RNG (tk_sh hdp) 1 -> ExecF.rng RNG (tk_sh TK_QD) 1 -> ExecF.rng RNG TK_QD 4 ->
  ExecF.rng RNG hdp 4 ->
  (* the cell at has_display is writable *)
  (exists junk, rw_cells rsegs m hdp [CB 4 junk]) ->
  (* the ranges read after a store lie off the stored ranges: off the frame, and the two reads of g_s's queued
     count off has_display *)
  off_stk sp TK_FRAME GOT_CELL_K 8 -> off_stk sp TK_FRAME CELL_K 8 -> off_stk sp TK_FRAME (tk_sh hdp) 1 ->
  off_stk sp TK_FRAME (tk_sh TK_QD) 1 -> off_stk sp TK_FRAME TK_QD 4 -> off_stk sp TK_FRAME hdp 4 ->
  (hdp + 4 <= tk_sh TK_QD \/ tk_sh TK_QD + 1 <= hdp) -> (hdp + 4 <= TK_QD \/ TK_QD + 4 <= hdp) ->
  (* the facts that decide the checks and the branch *)
  hdp mod 4 = 0 -> (khd = 0 \/ (hdp mod 8 + 3 < khd /\ khd < 8)) ->
  0 < queued <= 512 ->
  0 < bp -> bp + 1484 < 2 ^ 63 -> 0 < blp -> blp + 8 < 2 ^ 63 -> 0 < hdp -> hdp + 4 < 2 ^ 63 ->
  - 2 ^ 31 <= allow < 2 ^ 31 ->
  ExecF.evtF rsegs RNG
    (fun ms' => exists (m1 : word -> option byte) (x11 x12 x13 : word),
       ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - TK_FRAME)) gp tp (Z_to_bv 64 TK_MAXB)
                     (Z_to_bv 64 (tk_sh TK_MAXB)) t2 s0 (Z_to_bv 64 TK_QD) (Z_to_bv 64 1) x11 x12 x13
                     (Z_to_bv 64 TK_MAXC) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 TK_K) s2 (Z_to_bv 64 1)
                     (Z_to_bv 64 (tk_sh TK_MAXC)) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 TK_S) s8
                     (Z_to_bv 64 (tk_sh TK_QD)) s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 TK_L) fc None m1 (seg_rom rsegs) /\
       munch [(bv_unsigned sp - TK_FRAME, bv_unsigned sp); (hdp, hdp + 4)] m m1 /\ wmono rsegs m m1 /\
       stk rsegs m1 lo (bv_unsigned sp - TK_FRAME) /\
       rw_cells rsegs m1 hdp [C4 (Z_to_bv 64 0)] /\
       (exists j38, rw_cells rsegs m1 (bv_unsigned sp - TK_FRAME)
          (tk_fr (tk_spill bp blp hdp allow j38 ++ tk_saved s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 TK_S) (Z_to_bv 64 bp) (Z_to_bv 64 blp) (Z_to_bv 64 allow)
             (Z_to_bv 64 hdp) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 TK_ENTRY) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo bp blp hdp allow khd queued ST LO RFR RGC RCK GGC GCK RSH RSQ RQ GSH GSQ GQ GH CH O1 O2 O3 O4 O5 O6 D7 D8
    HM HK HQ HB0 HB1 HL0 HL1 HH0 HH1 HAL.
  destruct CH as [jh CH].
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  unfold off_stk in O1, O2, O3, O4, O5, O6.
  unfold GOT_CELL_K, CELL_K, ASAN_K, wa in RGC, RCK. unfold GOT_CELL_K, CELL_K in GGC, GCK, O1, O2.
  cbn [tk_fr tk_spill tk_saved map app].
  tk_lits.
  pose proof (munch_refl [(bv_unsigned sp - 224, bv_unsigned sp); (hdp, hdp + 4)] m) as MU.
  pose proof (munch_refl [(bv_unsigned sp - 224, bv_unsigned sp)] m) as MF.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 224%nat ST.
  destruct (tk_c8s 28 _ _ _ FR) as (ws & LW & FR'). clear FR.
  destruct (tk_len28 ws LW) as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 &
    w15 & w16 & w17 & w18 & w19 & w20 & w21 & w22 & w23 & w24 & w25 & w26 & w27 & ->).
  cbn [map] in FR'. rename FR' into FR.
  tk_pro MF RGC RCK RSH. tk_khd HK khd hdp; clear MF.
  - tk_pro2 MU RSQ RQ. tk_br false tk_cmp.
    (* +0x90 .. +0xf8: the spill of has_display, the counters, the cfg addresses and the spills of the loop *)
    do 27 step.
    tk_post. split; [tk_ms|]. split; [exact MU|]. split; [exact WM|]. split; [exact ST|]. split; [exact CH|].
    eexists. exact FR.
  - tk_pro2 MU RSQ RQ. tk_br false tk_cmp.
    do 27 step.
    tk_post. split; [tk_ms|]. split; [exact MU|]. split; [exact WM|]. split; [exact ST|]. split; [exact CH|].
    eexists. exact FR.
Qed.

(* ---- run 1z: the prologue with s->queued = 0, straight to the exit ---- *)

Lemma tk_run_entry_z : forall (RNG : ExecF.footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (lo bp blp hdp allow khd : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + TK_FRAME <= bv_unsigned sp ->
  ExecF.rng RNG (bv_unsigned sp - TK_FRAME) TK_FRAME ->
  ov_read_bytes rsegs m (wa GOT_CELL_K) 8 = Some (le8 (wa CELL_K)) ->
  ov_read_bytes rsegs m (wa CELL_K) 8 = Some (le8 (wa ASAN_K)) ->
  ExecF.rng RNG GOT_CELL_K 8 -> ExecF.rng RNG CELL_K 8 ->
  ov_read_bytes rsegs m (wa (tk_sh hdp)) 1 = Some [Z_to_bv 8 khd] ->
  ov_read_bytes rsegs m (wa (tk_sh TK_QD)) 1 = Some [Z_to_bv 8 0] ->
  ov_read_bytes rsegs m (wa TK_QD) 4 = Some (TW.put 4 0) ->
  ExecF.rng RNG (tk_sh hdp) 1 -> ExecF.rng RNG (tk_sh TK_QD) 1 -> ExecF.rng RNG TK_QD 4 ->
  ExecF.rng RNG hdp 4 ->
  (exists junk, rw_cells rsegs m hdp [CB 4 junk]) ->
  off_stk sp TK_FRAME GOT_CELL_K 8 -> off_stk sp TK_FRAME CELL_K 8 -> off_stk sp TK_FRAME (tk_sh hdp) 1 ->
  off_stk sp TK_FRAME (tk_sh TK_QD) 1 -> off_stk sp TK_FRAME TK_QD 4 -> off_stk sp TK_FRAME hdp 4 ->
  (hdp + 4 <= tk_sh TK_QD \/ tk_sh TK_QD + 1 <= hdp) -> (hdp + 4 <= TK_QD \/ TK_QD + 4 <= hdp) ->
  hdp mod 4 = 0 -> (khd = 0 \/ (hdp mod 8 + 3 < khd /\ khd < 8)) ->
  0 < bp -> bp + 1484 < 2 ^ 63 -> 0 < blp -> blp + 8 < 2 ^ 63 -> 0 < hdp -> hdp + 4 < 2 ^ 63 ->
  - 2 ^ 31 <= allow < 2 ^ 31 ->
  ExecF.evtF rsegs RNG
    (fun ms' => exists (m1 : word -> option byte) (x11 x13 x14 : word) (ws : list word),
       ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - TK_FRAME)) gp tp t0 t1 t2 s0 (Z_to_bv 64 TK_QD)
                     (Z_to_bv 64 0) x11 (Z_to_bv 64 blp) x13 x14 (Z_to_bv 64 0) (Z_to_bv 64 0)
                     (Z_to_bv 64 TK_K) s2 s3 s4 (Z_to_bv 64 0) s6 (Z_to_bv 64 TK_S) s8
                     (Z_to_bv 64 (tk_sh TK_QD)) s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 TK_X) fc None m1 (seg_rom rsegs) /\
       munch [(bv_unsigned sp - TK_FRAME, bv_unsigned sp); (hdp, hdp + 4)] m m1 /\ wmono rsegs m m1 /\
       stk rsegs m1 lo (bv_unsigned sp - TK_FRAME) /\
       rw_cells rsegs m1 hdp [C4 (Z_to_bv 64 0)] /\
       length ws = 15%nat /\ nth 5 ws (Z_to_bv 64 0) = Z_to_bv 64 blp /\
       rw_cells rsegs m1 (bv_unsigned sp - TK_FRAME)
         (tk_fr (ws ++ tk_saved s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 TK_S) (Z_to_bv 64 bp) (Z_to_bv 64 blp) (Z_to_bv 64 allow)
             (Z_to_bv 64 hdp) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 TK_ENTRY) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo bp blp hdp allow khd ST LO RFR RGC RCK GGC GCK RSH RSQ RQ GSH GSQ GQ GH CH O1 O2 O3 O4 O5 O6 D7 D8
    HM HK HB0 HB1 HL0 HL1 HH0 HH1 HAL.
  destruct CH as [jh CH].
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  unfold off_stk in O1, O2, O3, O4, O5, O6.
  unfold GOT_CELL_K, CELL_K, ASAN_K, wa in RGC, RCK. unfold GOT_CELL_K, CELL_K in GGC, GCK, O1, O2.
  tk_lits.
  pose proof (munch_refl [(bv_unsigned sp - 224, bv_unsigned sp); (hdp, hdp + 4)] m) as MU.
  pose proof (munch_refl [(bv_unsigned sp - 224, bv_unsigned sp)] m) as MF.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 224%nat ST.
  destruct (tk_c8s 28 _ _ _ FR) as (ws & LW & FR'). clear FR.
  destruct (tk_len28 ws LW) as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 &
    w15 & w16 & w17 & w18 & w19 & w20 & w21 & w22 & w23 & w24 & w25 & w26 & w27 & ->).
  cbn [map] in FR'. rename FR' into FR.
  tk_pro MF RGC RCK RSH. tk_khd HK khd hdp; clear MF.
  all: tk_pro2 MU RSQ RQ; tk_br true ltac:(vm_compute; reflexivity).
  (* +0x3b0 mv s5,zero; +0x3b4 mv a6,zero; +0x3b8 mv a5,zero; +0x3bc j +0x3cc *)
  all: do 4 step.
  all: apply evtF_done; cbv beta; do 4 eexists;
    exists [w0; w1; w2; Z_to_bv 64 (hdp / 8 + 2147450880); w4; Z_to_bv 64 blp; Z_to_bv 64 bp; w7;
            Z_to_bv 64 allow; w9; w10; w11; w12; w13; w14].
  all: split; [tk_ms|]; split; [exact MU|]; split; [exact WM|]; split; [exact ST|]; split; [exact CH|].
  all: split; [reflexivity|]; split; [reflexivity|].
  all: cbn [tk_fr tk_saved map app]; exact FR.
Qed.

(* ---- the loop head: the state of turn i ---- *)

(* The machine state at TK_L with the turn i of take_loop_m still to run: the free registers are ra, t2, s0, a1,
   a2, a3, s2, s8, s10, s11, t3 .. t6. *)
Definition tk_at_L (ra t2 s0 a1 a2 a3 s2 s8 s10 s11 t3 t4 t5 t6 : word) (gp tp F : _)
    (fc : bv 32) (m : word -> option byte) (sp' i taken kept len : Z) : machine_state :=
  MS (mkR ra (Z_to_bv 64 sp') gp tp (Z_to_bv 64 TK_MAXB) (Z_to_bv 64 (tk_sh TK_MAXB)) t2 s0
          (Z_to_bv 64 TK_QD) (Z_to_bv 64 (i + 1)) a1 a2 a3 (Z_to_bv 64 TK_MAXC) (Z_to_bv 64 taken)
          (Z_to_bv 64 len) (Z_to_bv 64 TK_K) s2 (Z_to_bv 64 (i + 1)) (Z_to_bv 64 (tk_sh TK_MAXC))
          (Z_to_bv 64 kept) (Z_to_bv 64 (32 * i)) (Z_to_bv 64 TK_S) s8 (Z_to_bv 64 (tk_sh TK_QD)) s10 s11
          t3 t4 t5 t6)
     F (Z_to_bv 64 TK_L) fc None m (seg_rom rsegs).

(* The state at TK_NF (the refusal). *)
Definition tk_at (pc : Z) (ra t2 s0 a0 a1 a2 a3 s2 s8 s10 s11 t3 t4 t5 t6 : word) (gp tp F : _)
    (fc : bv 32) (m : word -> option byte) (sp' i taken kept len : Z) : machine_state :=
  MS (mkR ra (Z_to_bv 64 sp') gp tp (Z_to_bv 64 TK_MAXB) (Z_to_bv 64 (tk_sh TK_MAXB)) t2
          (Z_to_bv 64 (i + 1)) (Z_to_bv 64 (tk_sh TK_QD)) a0 a1 a2 a3 (Z_to_bv 64 TK_MAXC)
          (Z_to_bv 64 taken) (Z_to_bv 64 len) (Z_to_bv 64 TK_K) (Z_to_bv 64 TK_QD) (Z_to_bv 64 (i + 1))
          (Z_to_bv 64 (tk_sh TK_MAXC)) (Z_to_bv 64 kept) (Z_to_bv 64 (32 * i)) (Z_to_bv 64 TK_S) s8
          (Z_to_bv 64 (TK_Q0 + 32 * i)) s10 s11 t3 t4 t5 t6)
     F (Z_to_bv 64 pc) fc None m (seg_rom rsegs).

(* The state at TK_J (the end of a turn): tk_at's registers, except s9, which both paths into TK_J set to s1, the
   shadow byte address of s->queued (`mv s9,s1` at +0x1d8 and +0x268). *)
Definition tk_at_J (ra t2 s0 a0 a1 a2 a3 s2 s8 s10 s11 t3 t4 t5 t6 : word) (gp tp F : _)
    (fc : bv 32) (m : word -> option byte) (sp' i taken kept len : Z) : machine_state :=
  MS (mkR ra (Z_to_bv 64 sp') gp tp (Z_to_bv 64 TK_MAXB) (Z_to_bv 64 (tk_sh TK_MAXB)) t2
          (Z_to_bv 64 (i + 1)) (Z_to_bv 64 (tk_sh TK_QD)) a0 a1 a2 a3 (Z_to_bv 64 TK_MAXC)
          (Z_to_bv 64 taken) (Z_to_bv 64 len) (Z_to_bv 64 TK_K) (Z_to_bv 64 TK_QD) (Z_to_bv 64 (i + 1))
          (Z_to_bv 64 (tk_sh TK_MAXC)) (Z_to_bv 64 kept) (Z_to_bv 64 (32 * i)) (Z_to_bv 64 TK_S) s8
          (Z_to_bv 64 (tk_sh TK_QD)) s10 s11 t3 t4 t5 t6)
     F (Z_to_bv 64 TK_J) fc None m (seg_rom rsegs).

(* ---- runs from the loop head ---- *)

(* The reads of turn i that every path makes: the two shadow bytes of the cfg fields, the shadow byte of
   c->len, the two cfg fields and c->len itself. All six lie in g_s's payload, so their shadow bytes are 0. *)
Definition tk_rd_turn (m : word -> option byte) (i clen disp maxc maxb : Z) : Prop :=
  ov_read_bytes rsegs m (wa (tk_sh TK_MAXC)) 1 = Some [Z_to_bv 8 0] /\
  ov_read_bytes rsegs m (wa (tk_sh TK_MAXB)) 1 = Some [Z_to_bv 8 0] /\
  ov_read_bytes rsegs m (wa (tk_sh (TK_Q0 + 32 * i + 24))) 1 = Some [Z_to_bv 8 0] /\
  ov_read_bytes rsegs m (wa (tk_sh (TK_Q0 + 32 * i + 25))) 1 = Some [Z_to_bv 8 0] /\
  ov_read_bytes rsegs m (wa TK_MAXC) 4 = Some (TW.put 4 maxc) /\
  ov_read_bytes rsegs m (wa TK_MAXB) 4 = Some (TW.put 4 maxb) /\
  ov_read_bytes rsegs m (wa (TK_Q0 + 32 * i + 24)) 1 = Some (TW.put 1 clen) /\
  ov_read_bytes rsegs m (wa (TK_Q0 + 32 * i + 25)) 1 = Some (TW.put 1 disp).

Definition tk_rng_turn (RNG : ExecF.footprint) (i : Z) : Prop :=
  ExecF.rng RNG (tk_sh TK_MAXC) 1 /\ ExecF.rng RNG (tk_sh TK_MAXB) 1 /\
  ExecF.rng RNG (tk_sh (TK_Q0 + 32 * i + 24)) 1 /\ ExecF.rng RNG (tk_sh (TK_Q0 + 32 * i + 25)) 1 /\
  ExecF.rng RNG TK_MAXC 4 /\ ExecF.rng RNG TK_MAXB 4 /\
  ExecF.rng RNG (TK_Q0 + 32 * i + 24) 1 /\ ExecF.rng RNG (TK_Q0 + 32 * i + 25) 1.

Definition tk_bounds (i taken kept len clen disp maxc maxb : Z) : Prop :=
  0 <= i < 512 /\ 0 <= taken <= 512 /\ 0 <= kept <= 512 /\ 0 <= len <= 1484 /\
  0 <= clen < 256 /\ 0 <= disp < 256 /\ 0 <= maxc < 2 ^ 32 /\ 0 <= maxb < 2 ^ 32.

(* +0x154 .. +0x174 of a turn that fits: the spill of taken, c->len under its shadow check, body + len, the call. *)
Local Ltac tk_fit_tail MU R3 R7 :=
  (* +0x154 sd a5,0x38(sp) *)
  step;
  (* +0x158 lb a0,0(s11): the shadow byte of c->len; +0x15c bnez a0 *)
  tk_rd MU R3; step; step; tk_br false ltac:(vm_compute; reflexivity);
  (* +0x160 lbu a2,0x6f8(s8): c->len; +0x164 ld s7,0x30(sp): body; +0x168 add a0,s7,a6; +0x16c mv a1,s9;
     +0x170 mv s4,a6; +0x174 the call *)
  tk_rd MU R7; step; rewrite tk_lbu_put by lia; step; step; step; step; step.

(* The turn fits the counters and the pacing: the walk reaches the copy of :365. *)
Lemma tk_run_fit : forall (RNG : ExecF.footprint)
    (ra t2 s0 a1 a2 a3 s2 s8 s10 s11 t3 t4 t5 t6 : word) (gp tp : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (sp' lo i taken kept len clen disp maxc maxb bp blp hdp allow : Z) (j38 sv : _),
  tk_rd_turn m i clen disp maxc maxb -> tk_rng_turn RNG i ->
  tk_bounds i taken kept len clen disp maxc maxb ->
  rw_cells rsegs m sp' (tk_fr (tk_spill bp blp hdp allow j38 ++ sv)) -> length sv = 13%nat ->
  ExecF.rng RNG sp' TK_FRAME -> stk rsegs m lo sp' -> lo <= sp' -> 0 <= sp' -> sp' + TK_FRAME < 2 ^ 63 ->
  0 < bp -> bp + 1484 < 2 ^ 63 -> - 2 ^ 31 <= allow < 2 ^ 31 ->
  taken < maxc -> len + clen <= maxb -> (allow <> 0 \/ disp = 0) ->
  (tk_sh (TK_Q0 + 32 * i + 24) + 1 <= sp' \/ sp' + TK_FRAME <= tk_sh (TK_Q0 + 32 * i + 24)) ->
  (TK_Q0 + 32 * i + 25 <= sp' \/ sp' + TK_FRAME <= TK_Q0 + 32 * i + 24) ->
  ExecF.evtF rsegs RNG
    (fun ms' => exists (m1 : word -> option byte) (y2 y3 : word),
       ms' = MS (mkR (Z_to_bv 64 TK_R1) (Z_to_bv 64 sp') gp tp (Z_to_bv 64 TK_MAXB)
                     (Z_to_bv 64 (tk_sh TK_MAXB)) y2 (Z_to_bv 64 (i + 1)) (Z_to_bv 64 (tk_sh TK_QD))
                     (Z_to_bv 64 (bp + len)) (Z_to_bv 64 (TK_Q0 + 32 * i)) (Z_to_bv 64 clen) y3
                     (Z_to_bv 64 TK_MAXC) (Z_to_bv 64 taken) (Z_to_bv 64 len) (Z_to_bv 64 TK_K)
                     (Z_to_bv 64 TK_QD) (Z_to_bv 64 (i + 1)) (Z_to_bv 64 len) (Z_to_bv 64 kept)
                     (Z_to_bv 64 (32 * i)) (Z_to_bv 64 bp) (Z_to_bv 64 (TK_S + 32 * i))
                     (Z_to_bv 64 (TK_Q0 + 32 * i)) (Z_to_bv 64 (TK_Q0 + 32 * i + 24))
                     (Z_to_bv 64 (tk_sh (TK_Q0 + 32 * i + 24))) t3 t4 t5 t6)
                F (Z_to_bv 64 TK_MEMCPY) fc None m1 (seg_rom rsegs) /\
       munch [(sp' + 0x38, sp' + 0x40)] m m1 /\ wmono rsegs m m1 /\ stk rsegs m1 lo sp' /\
       rw_cells rsegs m1 sp' (tk_fr (tk_spill bp blp hdp allow (Z_to_bv 64 taken) ++ sv)))
    (tk_at_L ra t2 s0 a1 a2 a3 s2 s8 s10 s11 t3 t4 t5 t6 gp tp F fc m sp' i taken kept len).
Proof.
  intros RNG ra t2 s0 a1 a2 a3 s2 s8 s10 s11 t3 t4 t5 t6 gp tp F fc m sp' lo i taken kept len clen disp maxc maxb
    bp blp hdp allow j38 sv RD RG BD FR LSV RFR ST HLO HS0 HS1 HB0 HB1 HAL HC HB HAD D24 D25.
  destruct RD as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8).
  destruct RG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
  destruct BD as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
  cbn [tk_fr tk_spill map app] in FR |- *.
  unfold tk_at_L. tk_lits.
  pose proof (munch_refl [(sp' + 56, sp' + 64)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (* +0xfc .. +0x10c: the shadow check of max_cmds *)
  step. step. step. step. step. tk_br false ltac:(vm_compute; reflexivity).
  (* +0x110 .. +0x11c: taken < max_cmds *)
  step. rewrite tk_lw_put. step. step. step. tk_br false tk_cmp.
  (* +0x120 .. +0x130: the shadow check of c->len *)
  step. replace (6158784 + 32 * i + 1784) with (6160544 + 32 * i + 24) by lia.
  step. rewrite tk_shr3 by lia. step.
  step. step. tk_br false ltac:(vm_compute; reflexivity).
  (* +0x134 .. +0x13c: c->len and the shadow check of max_body *)
  step. step. rewrite tk_lbu_put by lia. step. tk_br false ltac:(vm_compute; reflexivity).
  (* +0x140 .. +0x148: len + c->len <= max_body *)
  step. rewrite tk_lwu_put by lia. step. step. tk_br false tk_cmp.
  (* +0x14c ld a0,0x40(sp): allow_display; +0x150 beqz a0 *)
  step. step.
  destruct (Z.eq_dec allow 0) as [HA|HA].
  - (* allow_display = 0, so c->display = 0: +0x1fc .. +0x214 *)
    assert (HD : disp = 0) by (destruct HAD; [contradiction | exact H]).
    subst allow disp. tk_br true tk_cmp.
    step. replace (6158784 + 32 * i + 1785) with (6160544 + 32 * i + 25) by lia.
    step. rewrite tk_shr3 by lia. step. step.
    step. tk_br false ltac:(vm_compute; reflexivity).
    step. rewrite tk_lbu_put by lia. step. tk_br true tk_cmp.
    tk_fit_tail MU R3 R7.
    tk_post. split; [tk_ms|]. split; [exact MU|]. split; [exact WM|]. split; [exact ST | exact FR].
  - tk_br false tk_cmp.
    tk_fit_tail MU R3 R7.
    tk_post. split; [tk_ms|]. split; [exact MU|]. split; [exact WM|]. split; [exact ST | exact FR].
Qed.

(* The turn does not fit: taken reached max_cmds (:360). *)
Lemma tk_run_nofit_a : forall (RNG : ExecF.footprint)
    (ra t2 s0 a1 a2 a3 s2 s8 s10 s11 t3 t4 t5 t6 : word) (gp tp : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (sp' i taken kept len clen disp maxc maxb : Z),
  tk_rd_turn m i clen disp maxc maxb -> tk_rng_turn RNG i ->
  tk_bounds i taken kept len clen disp maxc maxb ->
  maxc <= taken ->
  ExecF.evtF rsegs RNG
    (fun ms' => exists (z0 z1 z26 z27 : word),
       ms' = tk_at TK_NF ra t2 s0 z0 z1 a2 a3 s2 (Z_to_bv 64 (TK_S + 32 * i)) z26 z27 t3 t4 t5 t6 gp tp F fc m
               sp' i taken kept len)
    (tk_at_L ra t2 s0 a1 a2 a3 s2 s8 s10 s11 t3 t4 t5 t6 gp tp F fc m sp' i taken kept len).
Proof.
  intros RNG ra t2 s0 a1 a2 a3 s2 s8 s10 s11 t3 t4 t5 t6 gp tp F fc m sp' i taken kept len clen disp maxc maxb
    RD RG BD HC.
  destruct RD as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8).
  destruct RG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
  destruct BD as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
  unfold tk_at_L, tk_at. tk_lits.
  (* +0xfc mv s2,s1; +0x100 mv s1,s9; +0x104 lb a1,0(s4): the shadow byte of max_cmds, 0 *)
  step. step. step.
  (* +0x108 mv s0,a0; +0x10c bnez a1 *)
  step. step. tk_br false ltac:(vm_compute; reflexivity).
  (* +0x110 lw a0,0(a4): max_cmds; +0x114 add s8,s7,s6; +0x118 addi s9,s8,0x6e0 *)
  step. rewrite tk_lw_put. step. step.
  (* +0x11c bgeu a5,a0: max_cmds <= taken *)
  step. tk_br true tk_cmp.
  tk_post. tk_ms.
Qed.

(* The turn does not fit: len + c->len passes max_body (:361). *)
Lemma tk_run_nofit_b : forall (RNG : ExecF.footprint)
    (ra t2 s0 a1 a2 a3 s2 s8 s10 s11 t3 t4 t5 t6 : word) (gp tp : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (sp' i taken kept len clen disp maxc maxb : Z),
  tk_rd_turn m i clen disp maxc maxb -> tk_rng_turn RNG i ->
  tk_bounds i taken kept len clen disp maxc maxb ->
  taken < maxc -> maxb < len + clen ->
  ExecF.evtF rsegs RNG
    (fun ms' => exists (z0 z1 z26 z27 : word),
       ms' = tk_at TK_NF ra t2 s0 z0 z1 a2 a3 s2 (Z_to_bv 64 (TK_S + 32 * i)) z26 z27 t3 t4 t5 t6 gp tp F fc m
               sp' i taken kept len)
    (tk_at_L ra t2 s0 a1 a2 a3 s2 s8 s10 s11 t3 t4 t5 t6 gp tp F fc m sp' i taken kept len).
Proof.
  intros RNG ra t2 s0 a1 a2 a3 s2 s8 s10 s11 t3 t4 t5 t6 gp tp F fc m sp' i taken kept len clen disp maxc maxb
    RD RG BD HC HB.
  destruct RD as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8).
  destruct RG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
  destruct BD as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
  unfold tk_at_L, tk_at. tk_lits.
  (* +0xfc .. +0x10c: the shadow check of max_cmds *)
  step. step. step. step. step. tk_br false ltac:(vm_compute; reflexivity).
  (* +0x110 .. +0x11c: taken < max_cmds *)
  step. rewrite tk_lw_put. step. step. step. tk_br false tk_cmp.
  (* +0x120 addi s10,s8,0x6f8; +0x124 srli; +0x128 add: s11 = the shadow byte address of c->len *)
  step. replace (6158784 + 32 * i + 1784) with (6160544 + 32 * i + 24) by lia.
  step. rewrite tk_shr3 by lia. step.
  (* +0x12c lb a0,0(s11); +0x130 bnez a0 *)
  step. step. tk_br false ltac:(vm_compute; reflexivity).
  (* +0x134 lb a1,0(t1): the shadow byte of max_body; +0x138 lbu a0,0x6f8(s8): c->len; +0x13c bnez a1 *)
  step. step. rewrite tk_lbu_put by lia. step. tk_br false ltac:(vm_compute; reflexivity).
  (* +0x140 lwu a1,0(t0): max_body; +0x144 add a0,a6,a0; +0x148 bltu a1,a0: max_body < len + c->len *)
  step. rewrite tk_lwu_put by lia. step. step. tk_br true tk_cmp.
  tk_post. tk_ms.
Qed.

(* The turn does not fit: the pacing (:362), allow_display = 0 and c->display <> 0. *)
Lemma tk_run_nofit_c : forall (RNG : ExecF.footprint)
    (ra t2 s0 a1 a2 a3 s2 s8 s10 s11 t3 t4 t5 t6 : word) (gp tp : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (sp' lo i taken kept len clen disp maxc maxb bp blp hdp allow : Z) (j38 sv : _),
  tk_rd_turn m i clen disp maxc maxb -> tk_rng_turn RNG i ->
  tk_bounds i taken kept len clen disp maxc maxb ->
  rw_cells rsegs m sp' (tk_fr (tk_spill bp blp hdp allow j38 ++ sv)) -> length sv = 13%nat ->
  ExecF.rng RNG sp' TK_FRAME -> 0 <= sp' -> sp' + TK_FRAME < 2 ^ 63 -> - 2 ^ 31 <= allow < 2 ^ 31 ->
  taken < maxc -> len + clen <= maxb -> allow = 0 -> disp <> 0 ->
  ExecF.evtF rsegs RNG
    (fun ms' => exists (z0 z1 z26 z27 : word),
       ms' = tk_at TK_NF ra t2 s0 z0 z1 a2 a3 s2 (Z_to_bv 64 (TK_S + 32 * i)) z26 z27 t3 t4 t5 t6 gp tp F fc m
               sp' i taken kept len)
    (tk_at_L ra t2 s0 a1 a2 a3 s2 s8 s10 s11 t3 t4 t5 t6 gp tp F fc m sp' i taken kept len).
Proof.
  intros RNG ra t2 s0 a1 a2 a3 s2 s8 s10 s11 t3 t4 t5 t6 gp tp F fc m sp' lo i taken kept len clen disp maxc maxb
    bp blp hdp allow j38 sv RD RG BD FR LSV RFR HS0 HS1 HAL HC HB HA HD.
  subst allow.
  destruct RD as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8).
  destruct RG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
  destruct BD as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
  cbn [tk_fr tk_spill map app] in FR.
  unfold tk_at_L, tk_at. tk_lits.
  (* +0xfc .. +0x10c: the shadow check of max_cmds *)
  step. step. step. step. step. tk_br false ltac:(vm_compute; reflexivity).
  (* +0x110 .. +0x11c: taken < max_cmds *)
  step. rewrite tk_lw_put. step. step. step. tk_br false tk_cmp.
  (* +0x120 .. +0x130: the shadow check of c->len *)
  step. replace (6158784 + 32 * i + 1784) with (6160544 + 32 * i + 24) by lia.
  step. rewrite tk_shr3 by lia. step.
  step. step. tk_br false ltac:(vm_compute; reflexivity).
  (* +0x134 .. +0x13c: c->len and the shadow check of max_body *)
  step. step. rewrite tk_lbu_put by lia. step. tk_br false ltac:(vm_compute; reflexivity).
  (* +0x140 .. +0x148: len + c->len <= max_body *)
  step. rewrite tk_lwu_put by lia. step. step. tk_br false tk_cmp.
  (* +0x14c ld a0,0x40(sp): allow_display = 0; +0x150 beqz a0 *)
  step. step. tk_br true ltac:(vm_compute; reflexivity).
  (* +0x1fc addi a0,s8,0x6f9; +0x200 srli; +0x204 add; +0x208 lb a1,0(a1): the shadow byte of c->display *)
  step. replace (6158784 + 32 * i + 1785) with (6160544 + 32 * i + 25) by lia.
  step. rewrite tk_shr3 by lia. step. step.
  (* +0x20c bnez a1; +0x210 lbu a0,0x6f9(s8): c->display; +0x214 beqz a0: c->display <> 0 *)
  step. tk_br false ltac:(vm_compute; reflexivity).
  step. rewrite tk_lbu_put by lia. step. tk_br false tk_cmp.
  tk_post. tk_ms.
Qed.

(* ---- the return of the copy of :365, to the call of diginet_body_check ---- *)

Lemma tk_run_bc_call : forall (RNG : ExecF.footprint)
    (ra t2 a3 s10 s11 t3 t4 t5 t6 : word) (gp tp : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (sp' i taken kept len clen bp : Z) (r0 r1 r2 r4 r5 r6 r7 x5 x6 : word),
  ov_read_bytes rsegs m (wa (TK_Q0 + 32 * i + 24)) 1 = Some (TW.put 1 clen) ->
  ExecF.rng RNG (TK_Q0 + 32 * i + 24) 1 ->
  0 <= i < 512 -> 0 <= clen < 256 -> 0 <= len <= 1484 -> 0 < bp -> bp + 1484 < 2 ^ 63 ->
  ExecF.evtF rsegs RNG
    (fun ms' => exists (y1 : word),
       ms' = MS (mkR (Z_to_bv 64 TK_R2) (Z_to_bv 64 sp') gp tp x5 x6 t2 (Z_to_bv 64 (i + 1))
                     (Z_to_bv 64 (tk_sh TK_QD)) (Z_to_bv 64 bp) (Z_to_bv 64 (len + clen)) y1 a3
                     r4 r5 r6 r7 (Z_to_bv 64 TK_QD) (Z_to_bv 64 (i + 1)) (Z_to_bv 64 len) (Z_to_bv 64 kept)
                     (Z_to_bv 64 (32 * i)) (Z_to_bv 64 bp) (Z_to_bv 64 (TK_S + 32 * i))
                     (Z_to_bv 64 (TK_Q0 + 32 * i)) (Z_to_bv 64 (TK_Q0 + 32 * i + 24))
                     (Z_to_bv 64 (tk_sh (TK_Q0 + 32 * i + 24))) t3 t4 t5 t6)
                F (Z_to_bv 64 TK_BC) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 sp') gp tp x5 x6 t2 (Z_to_bv 64 (i + 1))
             (Z_to_bv 64 (tk_sh TK_QD)) r0 r1 r2 a3 r4 r5 r6 r7 (Z_to_bv 64 TK_QD) (Z_to_bv 64 (i + 1))
             (Z_to_bv 64 len) (Z_to_bv 64 kept) (Z_to_bv 64 (32 * i)) (Z_to_bv 64 bp)
             (Z_to_bv 64 (TK_S + 32 * i)) (Z_to_bv 64 (TK_Q0 + 32 * i)) (Z_to_bv 64 (TK_Q0 + 32 * i + 24))
             (Z_to_bv 64 (tk_sh (TK_Q0 + 32 * i + 24))) t3 t4 t5 t6)
        F (Z_to_bv 64 TK_R1) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra t2 a3 s10 s11 t3 t4 t5 t6 gp tp F fc m sp' i taken kept len clen bp r0 r1 r2 r4 r5 r6 r7 x5 x6
    RC GC Hi Hc Hl Hb0 Hb1.
  tk_lits.
  (* +0x178 lbu a1,0x6f8(s8): c->len; +0x17c add a1,s4,a1; +0x180 mv a0,s7; +0x184 the call *)
  step. rewrite tk_lbu_put by lia. step. step. step.
  tk_post. tk_ms.
Qed.

(* ---- the return of diginet_body_check ---- *)

(* The state at TK_R2: the callee kept s0 .. s11, sp, gp and tp; a0 is its answer. *)
Definition tk_at_R2 (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (gp tp : word) (F : bvmap 5 word)
    (fc : bv 32) (m : word -> option byte) (sp' i taken kept len bp res : Z) : machine_state :=
  MS (mkR ra (Z_to_bv 64 sp') gp tp t0 t1 t2 (Z_to_bv 64 (i + 1))
          (Z_to_bv 64 (tk_sh TK_QD)) (Z_to_bv 64 res) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 TK_QD)
          (Z_to_bv 64 (i + 1)) (Z_to_bv 64 len) (Z_to_bv 64 kept) (Z_to_bv 64 (32 * i)) (Z_to_bv 64 bp)
          (Z_to_bv 64 (TK_S + 32 * i)) (Z_to_bv 64 (TK_Q0 + 32 * i)) (Z_to_bv 64 (TK_Q0 + 32 * i + 24))
          (Z_to_bv 64 (tk_sh (TK_Q0 + 32 * i + 24))) t3 t4 t5 t6)
     F (Z_to_bv 64 TK_R2) fc None m (seg_rom rsegs).

(* diginet_body_check refused the joined body: the turn refuses too (:366). *)
Lemma tk_run_bc_ne : forall (RNG : ExecF.footprint)
    (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (gp tp : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (sp' lo i taken kept len bp blp hdp allow res : Z) (sv : list word),
  rw_cells rsegs m sp' (tk_fr (tk_spill bp blp hdp allow (Z_to_bv 64 taken) ++ sv)) -> length sv = 13%nat ->
  ExecF.rng RNG sp' TK_FRAME -> stk rsegs m lo sp' -> 0 <= sp' -> sp' + TK_FRAME < 2 ^ 63 ->
  0 <= i < 512 -> 0 <= taken <= 512 -> 0 <= kept <= 512 -> 0 <= len <= 1484 -> res <> 0 ->
  - 2 ^ 31 <= res < 2 ^ 31 ->
  ExecF.evtF rsegs RNG
    (fun ms' => exists (z0 z1 z2 z3 z26 z27 : word),
       ms' = tk_at TK_NF ra t2 (Z_to_bv 64 (i + 1)) z0 z1 z2 z3 (Z_to_bv 64 TK_QD)
               (Z_to_bv 64 (TK_S + 32 * i)) z26 z27 t3 t4 t5 t6 gp tp F fc m sp' i taken kept len)
    (tk_at_R2 ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 gp tp F fc m sp' i taken kept len bp res).
Proof.
  intros RNG ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 gp tp F fc m sp' lo i taken kept len bp blp hdp allow
    res sv FR LSV RFR ST HS0 HS1 Hi Ht Hk Hl HR HRr.
  cbn [tk_fr tk_spill map app] in FR.
  unfold tk_at_R2, tk_at. tk_lits.
  (* +0x188 .. +0x1a4: len back in a6, the spills of the loop head back from the frame *)
  do 8 step.
  (* +0x1a8 bnez a0: the answer is not 0 *)
  step. tk_br true tk_cmp.
  tk_post. tk_ms.
Qed.

(* +0x1e0 .. +0x1f8 of an accepted turn: *has_display |= c->display, len += c->len, taken++, to TK_J. *)
Local Ltac tk_okt hd disp MU WM ST CH FR :=
  (* +0x1e0 ld a3,0x10(sp); +0x1e4 lw a2,0(a3): *has_display *)
  step; step; rewrite TTake.tk_sx32_small by lia;
  (* +0x1e8 add a6,a6,a1; +0x1ec addiw a5,a5,1; +0x1f0 or a0,a2,a0 *)
  step; step; rewrite tk_addiw by lia; step; rewrite ?(unsigned_lit hd), ?(unsigned_lit disp) by lia;
  (* +0x1f4 sw a0,0(a3); +0x1f8 j +0x26c *)
  step; step;
  tk_post; split; [tk_ms|]; split; [exact MU|]; split; [exact WM|]; split; [exact ST|]; split; [exact CH | exact FR].

(* diginet_body_check accepted: the turn takes the command (:368-371) and stores *has_display. *)
Lemma tk_run_bc_ok : forall (RNG : ExecF.footprint)
    (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (gp tp : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (sp' lo i taken kept len clen disp hd bp blp hdp allow khd : Z) (sv : list word),
  rw_cells rsegs m sp' (tk_fr (tk_spill bp blp hdp allow (Z_to_bv 64 taken) ++ sv)) -> length sv = 13%nat ->
  ExecF.rng RNG sp' TK_FRAME -> stk rsegs m lo sp' -> 0 <= sp' -> sp' + TK_FRAME < 2 ^ 63 ->
  ov_read_bytes rsegs m (wa (tk_sh (TK_Q0 + 32 * i + 24))) 1 = Some [Z_to_bv 8 0] ->
  ov_read_bytes rsegs m (wa (tk_sh (TK_Q0 + 32 * i + 25))) 1 = Some [Z_to_bv 8 0] ->
  ov_read_bytes rsegs m (wa (TK_Q0 + 32 * i + 24)) 1 = Some (TW.put 1 clen) ->
  ov_read_bytes rsegs m (wa (TK_Q0 + 32 * i + 25)) 1 = Some (TW.put 1 disp) ->
  ov_read_bytes rsegs m (wa (tk_sh hdp)) 1 = Some [Z_to_bv 8 khd] ->
  ov_read_bytes rsegs m (wa hdp) 4 = Some (TW.put 4 hd) ->
  ExecF.rng RNG (tk_sh (TK_Q0 + 32 * i + 24)) 1 -> ExecF.rng RNG (tk_sh (TK_Q0 + 32 * i + 25)) 1 ->
  ExecF.rng RNG (TK_Q0 + 32 * i + 24) 1 -> ExecF.rng RNG (TK_Q0 + 32 * i + 25) 1 ->
  ExecF.rng RNG (tk_sh hdp) 1 -> ExecF.rng RNG hdp 4 ->
  rw_cells rsegs m hdp [C4 (Z_to_bv 64 hd)] ->
  (hdp + 4 <= sp' \/ sp' + TK_FRAME <= hdp) ->
  hdp mod 4 = 0 -> (khd = 0 \/ (hdp mod 8 + 3 < khd /\ khd < 8)) ->
  0 < hdp -> hdp + 4 < 2 ^ 63 ->
  0 <= i < 512 -> 0 <= taken <= 512 -> 0 <= kept <= 512 -> 0 <= len <= 1484 -> 0 <= clen < 256 ->
  0 <= disp < 256 -> 0 <= hd < 256 ->
  ExecF.evtF rsegs RNG
    (fun ms' => exists (m1 : word -> option byte) (z0 z1 z2 z3 z24 z26 z27 : word),
       ms' = tk_at_J ra t2 (Z_to_bv 64 (i + 1)) z0 z1 z2 z3 z24 (Z_to_bv 64 (TK_S + 32 * i))
               z26 z27 t3 t4 t5 t6 gp tp F fc m1 sp' i (taken + 1) kept (len + clen) /\
       munch [(hdp, hdp + 4)] m m1 /\ wmono rsegs m m1 /\ stk rsegs m1 lo sp' /\
       rw_cells rsegs m1 hdp [C4 (Z_to_bv 64 (Z.lor hd disp))] /\
       rw_cells rsegs m1 sp' (tk_fr (tk_spill bp blp hdp allow (Z_to_bv 64 taken) ++ sv)))
    (tk_at_R2 ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 gp tp F fc m sp' i taken kept len bp 0).
Proof.
  intros RNG ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 gp tp F fc m sp' lo i taken kept len clen disp hd bp blp
    hdp allow khd sv FR LSV RFR ST HS0 HS1 RS4 RS5 RC RD RK RH GS4 GS5 GC GD GK GH CH DH HM HK Hh0 Hh1
    Hi Ht Hk Hl Hc Hd Hhd.
  destruct (tk_len13 sv LSV) as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & ->).
  cbn [tk_fr tk_spill map app] in FR |- *.
  unfold tk_at_R2, tk_at_J. tk_lits.
  pose proof (munch_refl [(hdp, hdp + 4)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (* +0x188 .. +0x1a4: len back in a6, the spills back *)
  do 8 step.
  (* +0x1a8 bnez a0: the answer is 0 *)
  step. tk_br false ltac:(vm_compute; reflexivity).
  (* +0x1ac lb a0,0(s11): the shadow byte of c->len; +0x1b0 bnez a0 *)
  step. step. tk_br false ltac:(vm_compute; reflexivity).
  (* +0x1b4 addi a0,s8,0x6f9; +0x1b8 srli; +0x1bc add; +0x1c0 lb a2,0(a1): the shadow byte of c->display *)
  step. replace (6158784 + 32 * i + 1785) with (6160544 + 32 * i + 25) by lia.
  step. rewrite tk_shr3 by lia. step. step.
  (* +0x1c4 lbu a1,0x6f8(s8): c->len; +0x1c8 bnez a2 *)
  step. rewrite tk_lbu_put by lia. step. tk_br false ltac:(vm_compute; reflexivity).
  (* +0x1cc ld a0,0x18(sp): the shadow byte address of has_display; +0x1d0 lb a2,0(a0);
     +0x1d4 lbu a0,0x6f9(s8): c->display; +0x1d8 mv s9,s1 *)
  step. step. step. rewrite tk_lbu_put by lia. step.
  (* +0x1dc bnez a2 *)
  step.
  destruct HK as [K0|[K1 K2]].
  - subst khd. tk_br false ltac:(vm_compute; reflexivity).
    tk_okt hd disp MU WM ST CH FR.
  - tk_br true ltac:(rewrite sxb_eq0, tk_signed8 by lia; tk_zc).
    (* +0x32c ld a3,0x10(sp); +0x330 andi a3,a3,7; +0x334 addi a3,a3,3; +0x338 blt a3,a2: back to +0x1e0 *)
    step. step. step. step.
    tk_br true ltac:(rewrite (unsigned_lit hdp), land7 by lia; rewrite lts_low by lia;
                     rewrite tk_signed8 by lia; tk_zc).
    tk_okt hd disp MU WM ST CH FR.
Qed.

(* ---- the refusal (:373-375) ---- *)

(* kept = i: no copy, kept++ only. *)
Lemma tk_run_nf_eq : forall (RNG : ExecF.footprint)
    (ra t2 a0 a1 a2 a3 s8 s10 s11 t3 t4 t5 t6 : word) (gp tp : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (sp' i taken kept len : Z),
  0 <= i < 512 -> 0 <= taken <= 512 -> 0 <= kept <= 512 -> 0 <= len <= 1484 -> kept = i ->
  ExecF.evtF rsegs RNG
    (fun ms' => exists (z0 z1 z24 : word),
       ms' = tk_at_J ra t2 (Z_to_bv 64 (i + 1)) z0 z1 a2 a3 z24 s8 s10 s11 t3 t4 t5 t6 gp tp F fc m
               sp' i taken (kept + 1) len)
    (tk_at TK_NF ra t2 (Z_to_bv 64 (i + 1)) a0 a1 a2 a3 (Z_to_bv 64 TK_QD) s8 s10 s11 t3 t4 t5 t6 gp tp F fc m
       sp' i taken kept len).
Proof.
  intros RNG ra t2 a0 a1 a2 a3 s8 s10 s11 t3 t4 t5 t6 gp tp F fc m sp' i taken kept len Hi Ht Hk Hl E.
  subst kept. unfold tk_at, tk_at_J. tk_lits.
  (* +0x218 addi a1,s0,-1; +0x21c slli a0,s5,32; +0x220 srli a0,a0,32: a1 = i, a0 = kept *)
  step. step. step. rewrite (TTake.tk_zext32 i) by lia.
  (* +0x224 beq a1,a0: kept = i *)
  step. tk_br true ltac:(apply bv_eqb_refl).
  (* +0x264 addi s5,s5,1; +0x268 mv s9,s1 *)
  step. step.
  tk_post. tk_ms.
Qed.

(* kept <> i: the copy of :374. *)
Lemma tk_run_nf_cpy : forall (RNG : ExecF.footprint)
    (ra t2 a0 a1 a2 a3 s8 s10 s11 t3 t4 t5 t6 : word) (gp tp : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (sp' i taken kept len bp blp hdp allow : Z) (j38 sv : _),
  rw_cells rsegs m sp' (tk_fr (tk_spill bp blp hdp allow j38 ++ sv)) -> length sv = 13%nat ->
  ExecF.rng RNG sp' TK_FRAME -> 0 <= sp' -> sp' + TK_FRAME < 2 ^ 63 ->
  0 <= i < 512 -> 0 <= taken <= 512 -> 0 <= kept < 512 -> 0 <= len <= 1484 -> kept <> i ->
  ExecF.evtF rsegs RNG
    (fun ms' => exists (y12 : word),
       ms' = MS (mkR (Z_to_bv 64 TK_R3) (Z_to_bv 64 sp') gp tp (Z_to_bv 64 TK_MAXB)
                     (Z_to_bv 64 (tk_sh TK_MAXB)) t2 (Z_to_bv 64 (i + 1)) (Z_to_bv 64 (tk_sh TK_QD))
                     (Z_to_bv 64 (TK_Q0 + 32 * kept)) (Z_to_bv 64 (TK_Q0 + 32 * i)) (Z_to_bv 64 32) y12
                     (Z_to_bv 64 TK_MAXC) (Z_to_bv 64 taken) (Z_to_bv 64 len) (Z_to_bv 64 TK_K)
                     (Z_to_bv 64 TK_QD) (Z_to_bv 64 (i + 1)) (Z_to_bv 64 len) (Z_to_bv 64 kept)
                     (Z_to_bv 64 (32 * i)) (Z_to_bv 64 TK_S) s8 (Z_to_bv 64 taken) s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 TK_MEMCPY) fc None m (seg_rom rsegs))
    (tk_at TK_NF ra t2 (Z_to_bv 64 (i + 1)) a0 a1 a2 a3 (Z_to_bv 64 TK_QD) s8 s10 s11 t3 t4 t5 t6 gp tp F fc m
       sp' i taken kept len).
Proof.
  intros RNG ra t2 a0 a1 a2 a3 s8 s10 s11 t3 t4 t5 t6 gp tp F fc m sp' i taken kept len bp blp hdp allow j38 sv
    FR LSV RFR HS0 HS1 Hi Ht Hk Hl HK.
  cbn [tk_fr tk_spill map app] in FR.
  unfold tk_at. tk_lits.
  (* +0x218 .. +0x220: a1 = i, a0 = kept; +0x224 beq a1,a0: kept <> i *)
  step. step. step. rewrite (TTake.tk_zext32 kept) by lia.
  step. tk_br false tk_cmp.
  (* +0x228 slli a0,a0,5; +0x22c ld a1,0x48(sp): &s->queue[0]; +0x230 add a0,a1,a0 *)
  step. rewrite tk_shl5 by lia. step. step.
  (* +0x234 li a2,32; +0x238 mv a1,s9; +0x23c mv s9,a5; +0x240 mv s4,a6; +0x244 the call *)
  step. step. step. step. step.
  tk_post. tk_ms.
Qed.

(* The return of the copy of :374: the spills come back, kept++. *)
Lemma tk_run_nf_ret : forall (RNG : ExecF.footprint)
    (ra t2 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 s8 s10 s11 t3 t4 t5 t6 : word) (gp tp : word) (F : bvmap 5 word)
    (fc : bv 32) (m : word -> option byte) (sp' lo i taken kept len bp blp hdp allow : Z) (j38 sv : _),
  rw_cells rsegs m sp' (tk_fr (tk_spill bp blp hdp allow j38 ++ sv)) -> length sv = 13%nat ->
  ExecF.rng RNG sp' TK_FRAME -> stk rsegs m lo sp' -> 0 <= sp' -> sp' + TK_FRAME < 2 ^ 63 ->
  0 <= i < 512 -> 0 <= taken <= 512 -> 0 <= kept < 512 -> 0 <= len <= 1484 ->
  ExecF.evtF rsegs RNG
    (fun ms' => exists (z0 z1 z24 : word),
       ms' = tk_at_J ra t2 (Z_to_bv 64 (i + 1)) z0 z1 a2 a3 z24 s8 s10 s11 t3 t4 t5 t6
               gp tp F fc m sp' i taken (kept + 1) len)
    (MS (mkR ra (Z_to_bv 64 sp') gp tp t0 t1 t2 (Z_to_bv 64 (i + 1))
             (Z_to_bv 64 (tk_sh TK_QD)) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 TK_QD) (Z_to_bv 64 (i + 1))
             (Z_to_bv 64 len) (Z_to_bv 64 kept) (Z_to_bv 64 (32 * i)) (Z_to_bv 64 TK_S) s8
             (Z_to_bv 64 taken) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 TK_R3) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra t2 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 s8 s10 s11 t3 t4 t5 t6 gp tp F fc m sp' lo i taken kept len bp
    blp hdp allow j38 sv FR LSV RFR ST HS0 HS1 Hi Ht Hk Hl.
  cbn [tk_fr tk_spill map app] in FR.
  unfold tk_at_J. tk_lits.
  (* +0x248 .. +0x260: the spills back, a6 = len, a5 = taken; +0x264 addi s5,s5,1; +0x268 mv s9,s1 *)
  do 9 step.
  tk_post. tk_ms.
Qed.

(* ---- the end of a turn (:377) ---- *)

(* The two cfg fields and s->queued, read again at the join. *)
Definition tk_rd_join (m : word -> option byte) (maxc maxb queued : Z) : Prop :=
  ov_read_bytes rsegs m (wa (tk_sh TK_MAXC)) 1 = Some [Z_to_bv 8 0] /\
  ov_read_bytes rsegs m (wa (tk_sh TK_MAXB)) 1 = Some [Z_to_bv 8 0] /\
  ov_read_bytes rsegs m (wa (tk_sh TK_QD)) 1 = Some [Z_to_bv 8 0] /\
  ov_read_bytes rsegs m (wa TK_MAXC) 4 = Some (TW.put 4 maxc) /\
  ov_read_bytes rsegs m (wa TK_MAXB) 4 = Some (TW.put 4 maxb) /\
  ov_read_bytes rsegs m (wa TK_QD) 4 = Some (TW.put 4 queued).

Definition tk_rng_join (RNG : ExecF.footprint) : Prop :=
  ExecF.rng RNG (tk_sh TK_MAXC) 1 /\ ExecF.rng RNG (tk_sh TK_MAXB) 1 /\ ExecF.rng RNG (tk_sh TK_QD) 1 /\
  ExecF.rng RNG TK_MAXC 4 /\ ExecF.rng RNG TK_MAXB 4 /\ ExecF.rng RNG TK_QD 4.

(* Neither counter is full and a turn is left: back to the loop head with i + 1. *)
Lemma tk_run_join_next : forall (RNG : ExecF.footprint)
    (ra t2 a0 a1 a2 a3 s8 s10 s11 t3 t4 t5 t6 : word) (gp tp : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (sp' i taken kept len maxc maxb queued : Z) (s9v : word),
  tk_rd_join m maxc maxb queued -> tk_rng_join RNG ->
  0 <= i < 512 -> 0 <= taken <= 512 -> 0 <= kept <= 512 -> 0 <= len <= 1484 ->
  0 <= maxc < 2 ^ 32 -> 0 <= maxb < 2 ^ 32 -> 0 <= queued <= 512 ->
  taken <> maxc -> len <> maxb -> i + 1 < queued ->
  ExecF.evtF rsegs RNG
    (fun ms' => exists (z0 z1 z2 z7 : word),
       ms' = tk_at_L ra t2 z7 z0 z1 a3 z2 s8 s10 s11 t3 t4 t5 t6 gp tp F fc m sp' (i + 1) taken kept len)
    (tk_at_J ra t2 (Z_to_bv 64 (i + 1)) a0 a1 a2 a3 s9v s8 s10 s11 t3 t4 t5 t6 gp tp F fc m
       sp' i taken kept len).
Proof.
  intros RNG ra t2 a0 a1 a2 a3 s8 s10 s11 t3 t4 t5 t6 gp tp F fc m sp' i taken kept len maxc maxb queued s9v
    RD RG Hi Ht Hk Hl HC HB HQ HTC HLB HN.
  destruct RD as (J1 & J2 & J3 & J4 & J5 & J6). destruct RG as (K1 & K2 & K3 & K4 & K5 & K6).
  unfold tk_at_J, tk_at_L. tk_lits.
  (* +0x26c mv s1,s2; +0x270 lb a0,0(s4): the shadow byte of max_cmds; +0x274 bnez a0 *)
  step. step. step. tk_br false ltac:(vm_compute; reflexivity).
  (* +0x278 lw a0,0(a4): max_cmds; +0x27c beq a5,a0: taken <> max_cmds *)
  step. rewrite tk_lw_put. step. tk_br false tk_cmp.
  (* +0x280 lb a0,0(t1): the shadow byte of max_body; +0x284 bnez a0 *)
  step. step. tk_br false ltac:(vm_compute; reflexivity).
  (* +0x288 lwu a0,0(t0): max_body; +0x28c beq a6,a0: len <> max_body *)
  step. rewrite tk_lwu_put by lia. step. tk_br false tk_cmp.
  (* +0x290 lb a0,0(s9): the shadow byte of s->queued; +0x294 bnez a0 *)
  step. step. tk_br false ltac:(vm_compute; reflexivity).
  (* +0x298 lwu a1,0(s1): s->queued; +0x29c addi a0,s0,1; +0x2a0 addi s6,s6,32; +0x2a4 addiw s3,s3,1 *)
  step. rewrite tk_lwu_put by lia. step. step. step.
  rewrite tk_addiw by lia.
  (* +0x2a8 bltu s0,a1: i + 1 < s->queued *)
  step. tk_br true tk_cmp.
  tk_post. tk_ms.
Qed.

(* Neither counter is full and no turn is left: the exit. *)
Lemma tk_run_join_exit : forall (RNG : ExecF.footprint)
    (ra t2 a0 a1 a2 a3 s8 s10 s11 t3 t4 t5 t6 : word) (gp tp : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (sp' i taken kept len maxc maxb queued : Z) (s9v : word),
  tk_rd_join m maxc maxb queued -> tk_rng_join RNG ->
  0 <= i < 512 -> 0 <= taken <= 512 -> 0 <= kept <= 512 -> 0 <= len <= 1484 ->
  0 <= maxc < 2 ^ 32 -> 0 <= maxb < 2 ^ 32 -> 0 <= queued <= 512 ->
  taken <> maxc -> len <> maxb -> queued <= i + 1 ->
  ExecF.evtF rsegs RNG
    (fun ms' => exists (z0 z1 z2 z7 z22 z23 z24 : word),
       ms' = MS (mkR ra (Z_to_bv 64 sp') gp tp (Z_to_bv 64 TK_MAXB) (Z_to_bv 64 (tk_sh TK_MAXB)) t2 z7
                     (Z_to_bv 64 TK_QD) z0 z1 a2 a3 (Z_to_bv 64 TK_MAXC) (Z_to_bv 64 taken) (Z_to_bv 64 len)
                     (Z_to_bv 64 TK_K) (Z_to_bv 64 TK_QD) z2 (Z_to_bv 64 (tk_sh TK_MAXC)) (Z_to_bv 64 kept)
                     z22 z23 z24 (Z_to_bv 64 (tk_sh TK_QD)) s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 TK_X) fc None m (seg_rom rsegs))
    (tk_at_J ra t2 (Z_to_bv 64 (i + 1)) a0 a1 a2 a3 s9v s8 s10 s11 t3 t4 t5 t6 gp tp F fc m
       sp' i taken kept len).
Proof.
  intros RNG ra t2 a0 a1 a2 a3 s8 s10 s11 t3 t4 t5 t6 gp tp F fc m sp' i taken kept len maxc maxb queued s9v
    RD RG Hi Ht Hk Hl HC HB HQ HTC HLB HN.
  destruct RD as (J1 & J2 & J3 & J4 & J5 & J6). destruct RG as (K1 & K2 & K3 & K4 & K5 & K6).
  unfold tk_at_J. tk_lits.
  (* +0x26c .. +0x27c: taken <> max_cmds *)
  step. step. step. tk_br false ltac:(vm_compute; reflexivity).
  step. rewrite tk_lw_put. step. tk_br false tk_cmp.
  (* +0x280 .. +0x28c: len <> max_body *)
  step. step. tk_br false ltac:(vm_compute; reflexivity).
  step. rewrite tk_lwu_put by lia. step. tk_br false tk_cmp.
  (* +0x290 .. +0x2a4: s->queued, the next turn's counters *)
  step. step. tk_br false ltac:(vm_compute; reflexivity).
  step. rewrite tk_lwu_put by lia. step. step. step. rewrite tk_addiw by lia.
  (* +0x2a8 bltu s0,a1: s->queued <= i + 1; +0x2ac j +0x3cc *)
  step. tk_br false tk_cmp. step.
  tk_post. tk_ms.
Qed.

(* A counter is full: the break of :377, to the tail. *)
Lemma tk_run_join_break : forall (RNG : ExecF.footprint)
    (ra t2 a0 a1 a2 a3 s8 s10 s11 t3 t4 t5 t6 : word) (gp tp : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (sp' i taken kept len maxc maxb queued : Z) (s9v : word),
  tk_rd_join m maxc maxb queued -> tk_rng_join RNG ->
  0 <= i < 512 -> 0 <= taken <= 512 -> 0 <= kept <= 512 -> 0 <= len <= 1484 ->
  0 <= maxc < 2 ^ 32 -> 0 <= maxb < 2 ^ 32 -> 0 <= queued <= 512 ->
  (taken = maxc \/ len = maxb) ->
  ExecF.evtF rsegs RNG
    (fun ms' => exists (z0 z1 : word),
       ms' = MS (mkR ra (Z_to_bv 64 sp') gp tp (Z_to_bv 64 TK_MAXB) (Z_to_bv 64 (tk_sh TK_MAXB)) t2
                     (Z_to_bv 64 (i + 1)) (Z_to_bv 64 TK_QD) z0 z1 a2 a3 (Z_to_bv 64 TK_MAXC)
                     (Z_to_bv 64 taken) (Z_to_bv 64 len) (Z_to_bv 64 TK_K) (Z_to_bv 64 TK_QD)
                     (Z_to_bv 64 (i + 1)) (Z_to_bv 64 (tk_sh TK_MAXC)) (Z_to_bv 64 kept)
                     (Z_to_bv 64 (32 * i)) (Z_to_bv 64 TK_S) s8 (Z_to_bv 64 (tk_sh TK_QD)) s10 s11
                     t3 t4 t5 t6)
                F (Z_to_bv 64 TK_BRK) fc None m (seg_rom rsegs))
    (tk_at_J ra t2 (Z_to_bv 64 (i + 1)) a0 a1 a2 a3 s9v s8 s10 s11 t3 t4 t5 t6 gp tp F fc m
       sp' i taken kept len).
Proof.
  intros RNG ra t2 a0 a1 a2 a3 s8 s10 s11 t3 t4 t5 t6 gp tp F fc m sp' i taken kept len maxc maxb queued s9v
    RD RG Hi Ht Hk Hl HC HB HQ HF.
  destruct RD as (J1 & J2 & J3 & J4 & J5 & J6). destruct RG as (K1 & K2 & K3 & K4 & K5 & K6).
  unfold tk_at_J. tk_lits.
  (* +0x26c .. +0x278: the shadow check of max_cmds, max_cmds *)
  step. step. step. tk_br false ltac:(vm_compute; reflexivity).
  step. rewrite tk_lw_put. step.
  destruct (Z.eq_dec taken maxc) as [E|E].
  - (* +0x27c beq a5,a0: taken = max_cmds *)
    tk_br true tk_cmp.
    tk_post. tk_ms.
  - (* taken <> max_cmds, so len = max_body: +0x280 .. +0x28c *)
    assert (EB : len = maxb) by (destruct HF; [contradiction | exact H]).
    tk_br false tk_cmp.
    step. step. tk_br false ltac:(vm_compute; reflexivity).
    step. rewrite tk_lwu_put by lia. step. tk_br true tk_cmp.
    tk_post. tk_ms.
Qed.

(* ---- the tail (:378-380) ---- *)

(* The state at the tail loop head, turn j: s0 = j, s2 = taken, s3 = &s->queue[j], s5 = kept, s6 = len,
   s7 = &s->queue[0]. t0, t1 and a4 .. a7 are free: the loop never reads them, and each copy clobbers them. *)
Definition tk_at_TL (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s8 s10 s11 t3 t4 t5 t6 : word) (gp tp : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (sp' j taken kept len : Z) : machine_state :=
  MS (mkR ra (Z_to_bv 64 sp') gp tp t0 t1 t2 (Z_to_bv 64 j)
          (Z_to_bv 64 TK_QD) a0 a1 a2 a3 a4 a5 a6 a7
          (Z_to_bv 64 taken) (Z_to_bv 64 (TK_Q0 + 32 * j)) s4 (Z_to_bv 64 kept)
          (Z_to_bv 64 len) (Z_to_bv 64 TK_Q0) s8 (Z_to_bv 64 (tk_sh TK_QD)) s10 s11 t3 t4 t5 t6)
     F (Z_to_bv 64 TK_TL) fc None m (seg_rom rsegs).

(* The break's own code: a turn is left, so the tail loop runs from j = i + 1. *)
Lemma tk_run_break_tail : forall (RNG : ExecF.footprint)
    (ra t2 a0 a1 a2 a3 s10 s11 t3 t4 t5 t6 : word) (gp tp : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (sp' lo i taken kept len queued bp blp hdp allow : Z) (j38 sv : _),
  rw_cells rsegs m sp' (tk_fr (tk_spill bp blp hdp allow j38 ++ sv)) -> length sv = 13%nat ->
  ExecF.rng RNG sp' TK_FRAME -> stk rsegs m lo sp' -> 0 <= sp' -> sp' + TK_FRAME < 2 ^ 63 ->
  ov_read_bytes rsegs m (wa (tk_sh TK_QD)) 1 = Some [Z_to_bv 8 0] ->
  ov_read_bytes rsegs m (wa TK_QD) 4 = Some (TW.put 4 queued) ->
  ExecF.rng RNG (tk_sh TK_QD) 1 -> ExecF.rng RNG TK_QD 4 ->
  0 <= i < 512 -> 0 <= taken <= 512 -> 0 <= kept <= 512 -> 0 <= len <= 1484 -> 0 <= queued <= 512 ->
  i + 1 < queued ->
  ExecF.evtF rsegs RNG
    (fun ms' => exists (z0 z1 z20 : word),
       ms' = tk_at_TL ra (Z_to_bv 64 TK_MAXB) (Z_to_bv 64 (tk_sh TK_MAXB)) t2 z0 z1 a2 a3 (Z_to_bv 64 TK_MAXC)
               (Z_to_bv 64 taken) (Z_to_bv 64 len) (Z_to_bv 64 TK_K) z20 (Z_to_bv 64 (TK_S + 32 * i)) s10 s11
               t3 t4 t5 t6 gp tp F fc m sp' (i + 1) taken kept len)
    (MS (mkR ra (Z_to_bv 64 sp') gp tp (Z_to_bv 64 TK_MAXB) (Z_to_bv 64 (tk_sh TK_MAXB)) t2
             (Z_to_bv 64 (i + 1)) (Z_to_bv 64 TK_QD) a0 a1 a2 a3 (Z_to_bv 64 TK_MAXC) (Z_to_bv 64 taken)
             (Z_to_bv 64 len) (Z_to_bv 64 TK_K) (Z_to_bv 64 TK_QD) (Z_to_bv 64 (i + 1))
             (Z_to_bv 64 (tk_sh TK_MAXC)) (Z_to_bv 64 kept) (Z_to_bv 64 (32 * i)) (Z_to_bv 64 TK_S)
             (Z_to_bv 64 (TK_S + 32 * i))
             (Z_to_bv 64 (tk_sh TK_QD)) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 TK_BRK) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra t2 a0 a1 a2 a3 s10 s11 t3 t4 t5 t6 gp tp F fc m sp' lo i taken kept len queued bp blp hdp allow
    j38 sv FR LSV RFR ST HS0 HS1 RS RQ GS GQ Hi Ht Hk Hl HQ HN.
  cbn [tk_fr tk_spill map app] in FR.
  unfold tk_at_TL. tk_lits.
  (* +0x344 lb a0,0(s9): the shadow byte of s->queued; +0x348 bnez a0 *)
  step. step. tk_br false ltac:(vm_compute; reflexivity).
  (* +0x34c lw a0,0(s1): s->queued; +0x350 ld s7,0x48(sp): &s->queue[0]; +0x354 bgeu s3,a0: i + 1 < s->queued *)
  step. rewrite tk_lw_put, tk_s32_small by lia. step. step. tk_br false tk_cmp.
  (* +0x358 mv s6,a6; +0x35c mv s2,a5; +0x360 addi s3,s8,0x700; +0x364 andi s4,s1,7; +0x368 addi s4,s4,3 *)
  do 5 step.
  tk_post. tk_ms.
Qed.

(* The break with no turn left: straight to the exit. *)
Lemma tk_run_break_exit : forall (RNG : ExecF.footprint)
    (ra t2 a0 a1 a2 a3 s8 s10 s11 t3 t4 t5 t6 : word) (gp tp : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (sp' lo i taken kept len queued bp blp hdp allow : Z) (j38 sv : _),
  rw_cells rsegs m sp' (tk_fr (tk_spill bp blp hdp allow j38 ++ sv)) -> length sv = 13%nat ->
  ExecF.rng RNG sp' TK_FRAME -> stk rsegs m lo sp' -> 0 <= sp' -> sp' + TK_FRAME < 2 ^ 63 ->
  ov_read_bytes rsegs m (wa (tk_sh TK_QD)) 1 = Some [Z_to_bv 8 0] ->
  ov_read_bytes rsegs m (wa TK_QD) 4 = Some (TW.put 4 queued) ->
  ExecF.rng RNG (tk_sh TK_QD) 1 -> ExecF.rng RNG TK_QD 4 ->
  0 <= i < 512 -> 0 <= taken <= 512 -> 0 <= kept <= 512 -> 0 <= len <= 1484 -> 0 <= queued <= 512 ->
  queued <= i + 1 ->
  ExecF.evtF rsegs RNG
    (fun ms' => exists (z0 z1 z22 z23 : word),
       ms' = MS (mkR ra (Z_to_bv 64 sp') gp tp (Z_to_bv 64 TK_MAXB) (Z_to_bv 64 (tk_sh TK_MAXB)) t2
                     (Z_to_bv 64 (i + 1)) (Z_to_bv 64 TK_QD) z0 z1 a2 a3 (Z_to_bv 64 TK_MAXC)
                     (Z_to_bv 64 taken) (Z_to_bv 64 len) (Z_to_bv 64 TK_K) (Z_to_bv 64 TK_QD)
                     (Z_to_bv 64 (i + 1)) (Z_to_bv 64 (tk_sh TK_MAXC)) (Z_to_bv 64 kept) z22 z23 s8
                     (Z_to_bv 64 (tk_sh TK_QD)) s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 TK_X) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 sp') gp tp (Z_to_bv 64 TK_MAXB) (Z_to_bv 64 (tk_sh TK_MAXB)) t2
             (Z_to_bv 64 (i + 1)) (Z_to_bv 64 TK_QD) a0 a1 a2 a3 (Z_to_bv 64 TK_MAXC) (Z_to_bv 64 taken)
             (Z_to_bv 64 len) (Z_to_bv 64 TK_K) (Z_to_bv 64 TK_QD) (Z_to_bv 64 (i + 1))
             (Z_to_bv 64 (tk_sh TK_MAXC)) (Z_to_bv 64 kept) (Z_to_bv 64 (32 * i)) (Z_to_bv 64 TK_S) s8
             (Z_to_bv 64 (tk_sh TK_QD)) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 TK_BRK) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra t2 a0 a1 a2 a3 s8 s10 s11 t3 t4 t5 t6 gp tp F fc m sp' lo i taken kept len queued bp blp hdp allow
    j38 sv FR LSV RFR ST HS0 HS1 RS RQ GS GQ Hi Ht Hk Hl HQ HN.
  cbn [tk_fr tk_spill map app] in FR.
  tk_lits.
  (* +0x344 lb a0,0(s9): the shadow byte of s->queued; +0x348 bnez a0 *)
  step. step. tk_br false ltac:(vm_compute; reflexivity).
  (* +0x34c lw a0,0(s1): s->queued; +0x350 ld s7,0x48(sp); +0x354 bgeu s3,a0: s->queued <= i + 1 *)
  step. rewrite tk_lw_put, tk_s32_small by lia. step. step. tk_br true tk_cmp.
  tk_post. tk_ms.
Qed.

(* The tail turn: the copy of :379. *)
Lemma tk_run_tail_cpy : forall (RNG : ExecF.footprint)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s8 s10 s11 t3 t4 t5 t6 : word) (gp tp : word) (F : bvmap 5 word)
    (fc : bv 32) (m : word -> option byte) (sp' j taken kept len : Z),
  0 <= j < 512 -> 0 <= taken <= 512 -> 0 <= kept < 512 -> 0 <= len <= 1484 ->
  ExecF.evtF rsegs RNG
    (fun ms' =>
       ms' = MS (mkR (Z_to_bv 64 TK_R4) (Z_to_bv 64 sp') gp tp t0 t1 t2 (Z_to_bv 64 j) (Z_to_bv 64 TK_QD)
                     (Z_to_bv 64 (TK_Q0 + 32 * kept)) (Z_to_bv 64 (TK_Q0 + 32 * j)) (Z_to_bv 64 32) a3
                     a4 a5 a6 a7
                     (Z_to_bv 64 taken) (Z_to_bv 64 (TK_Q0 + 32 * j)) s4 (Z_to_bv 64 kept) (Z_to_bv 64 len)
                     (Z_to_bv 64 TK_Q0) s8 (Z_to_bv 64 (tk_sh TK_QD)) s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 TK_MEMCPY) fc None m (seg_rom rsegs))
    (tk_at_TL ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s8 s10 s11 t3 t4 t5 t6 gp tp F fc m sp' j taken kept len).
Proof.
  intros RNG ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s8 s10 s11 t3 t4 t5 t6 gp tp F fc m sp' j taken kept len
    Hj Ht Hk Hl.
  unfold tk_at_TL. tk_lits.
  (* +0x36c slli a0,s5,32; +0x370 srli a0,a0,27: 32 * kept; +0x374 add a0,s7,a0 *)
  step. step. rewrite (TTake.tk_zext_shl5 kept) by lia. step.
  (* +0x378 li a2,32; +0x37c mv a1,s3; +0x380 the call *)
  step. step. step.
  tk_post. tk_ms.
Qed.

(* The return of the tail copy, with a turn left. *)
Lemma tk_run_tail_next : forall (RNG : ExecF.footprint)
    (ra t2 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 s4 s8 s10 s11 t3 t4 t5 t6 : word) (gp tp : word) (F : bvmap 5 word)
    (fc : bv 32) (m : word -> option byte) (sp' j taken kept len queued : Z),
  ov_read_bytes rsegs m (wa (tk_sh TK_QD)) 1 = Some [Z_to_bv 8 0] ->
  ov_read_bytes rsegs m (wa TK_QD) 4 = Some (TW.put 4 queued) ->
  ExecF.rng RNG (tk_sh TK_QD) 1 -> ExecF.rng RNG TK_QD 4 ->
  0 <= j < 512 -> 0 <= taken <= 512 -> 0 <= kept < 512 -> 0 <= len <= 1484 -> 0 <= queued <= 512 ->
  j + 1 < queued ->
  ExecF.evtF rsegs RNG
    (fun ms' => exists (z0 z1 : word),
       ms' = tk_at_TL ra t0 t1 t2 z0 z1 a2 a3 a4 a5 a6 a7 s4 s8 s10 s11 t3 t4 t5 t6 gp tp F fc m
               sp' (j + 1) taken (kept + 1) len)
    (MS (mkR ra (Z_to_bv 64 sp') gp tp t0 t1 t2 (Z_to_bv 64 j) (Z_to_bv 64 TK_QD) a0 a1 a2 a3
             a4 a5 a6 a7 (Z_to_bv 64 taken) (Z_to_bv 64 (TK_Q0 + 32 * j)) s4 (Z_to_bv 64 kept)
             (Z_to_bv 64 len) (Z_to_bv 64 TK_Q0) s8 (Z_to_bv 64 (tk_sh TK_QD)) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 TK_R4) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra t2 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 s4 s8 s10 s11 t3 t4 t5 t6 gp tp F fc m sp' j taken kept len queued
    RS RQ GS GQ Hj Ht Hk Hl HQ HN.
  unfold tk_at_TL. tk_lits.
  (* +0x384 lb a0,0(s9): the shadow byte of s->queued; +0x388 bnez a0 *)
  step. step. tk_br false ltac:(vm_compute; reflexivity).
  (* +0x38c lwu a0,0(s1): s->queued; +0x390 addi s0,s0,1; +0x394 addi s3,s3,32; +0x398 addi s5,s5,1 *)
  step. rewrite tk_lwu_put by lia. step. step. step.
  (* +0x39c bltu s0,a0: j + 1 < s->queued *)
  step. tk_br true tk_cmp.
  tk_post. tk_ms.
Qed.

(* The return of the tail copy, with no turn left: the exit. *)
Lemma tk_run_tail_done : forall (RNG : ExecF.footprint)
    (ra t2 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 s4 s8 s10 s11 t3 t4 t5 t6 : word) (gp tp : word) (F : bvmap 5 word)
    (fc : bv 32) (m : word -> option byte) (sp' lo j taken kept len queued bp blp hdp allow : Z) (j38 sv : _),
  rw_cells rsegs m sp' (tk_fr (tk_spill bp blp hdp allow j38 ++ sv)) -> length sv = 13%nat ->
  ExecF.rng RNG sp' TK_FRAME -> stk rsegs m lo sp' -> 0 <= sp' -> sp' + TK_FRAME < 2 ^ 63 ->
  ov_read_bytes rsegs m (wa (tk_sh TK_QD)) 1 = Some [Z_to_bv 8 0] ->
  ov_read_bytes rsegs m (wa TK_QD) 4 = Some (TW.put 4 queued) ->
  ExecF.rng RNG (tk_sh TK_QD) 1 -> ExecF.rng RNG TK_QD 4 ->
  0 <= j < 512 -> 0 <= taken <= 512 -> 0 <= kept < 512 -> 0 <= len <= 1484 -> 0 <= queued <= 512 ->
  queued <= j + 1 ->
  ExecF.evtF rsegs RNG
    (fun ms' => exists (z0 z1 z19 z22 z23 : word),
       ms' = MS (mkR ra (Z_to_bv 64 sp') gp tp t0 t1 t2 (Z_to_bv 64 (j + 1))
                     (Z_to_bv 64 TK_QD) z0 z1 a2 a3 a4 (Z_to_bv 64 taken) (Z_to_bv 64 len)
                     (Z_to_bv 64 TK_K) (Z_to_bv 64 taken) z19 s4 (Z_to_bv 64 (kept + 1)) z22 z23 s8
                     (Z_to_bv 64 (tk_sh TK_QD)) s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 TK_X) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 sp') gp tp t0 t1 t2 (Z_to_bv 64 j) (Z_to_bv 64 TK_QD) a0 a1 a2 a3
             a4 a5 a6 a7 (Z_to_bv 64 taken) (Z_to_bv 64 (TK_Q0 + 32 * j)) s4 (Z_to_bv 64 kept)
             (Z_to_bv 64 len) (Z_to_bv 64 TK_Q0) s8 (Z_to_bv 64 (tk_sh TK_QD)) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 TK_R4) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra t2 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 s4 s8 s10 s11 t3 t4 t5 t6 gp tp F fc m sp' lo j taken kept len
    queued bp blp hdp allow j38 sv FR LSV RFR ST HS0 HS1 RS RQ GS GQ Hj Ht Hk Hl HQ HN.
  cbn [tk_fr tk_spill map app] in FR.
  tk_lits.
  (* +0x384 .. +0x398 as in tk_run_tail_next *)
  step. step. tk_br false ltac:(vm_compute; reflexivity).
  step. rewrite tk_lwu_put by lia. step. step. step.
  (* +0x39c bltu s0,a0: s->queued <= j + 1; +0x3a0 j +0x3c0 *)
  step. tk_br false tk_cmp. step.
  (* +0x3c0 ld a7,0x70(sp); +0x3c4 mv a5,s2; +0x3c8 mv a6,s6 *)
  step. step. step.
  tk_post. tk_ms.
Qed.

(* ---- the exit (:383-385) ---- *)

(* s->queued = kept, *body_len = len, a0 = taken, the epilogue. The 4-byte store at s->queued and the 8-byte store
   at body_len are the last two writes; the saved registers come back from the frame. *)
Lemma tk_run_exit : forall (RNG : ExecF.footprint)
    (ra0 t2 a0 a1 a2 a3 a4 t0 t1 s0 s2 s3 s4 s6 s7 s8 s10 s11 t3 t4 t5 t6 : word) (gp tp : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (sp' lo taken kept len blp kbl queued0 : Z) (ws : list word)
    (v11 v10 v9 v8 v7 v6 v5 v4 v3 v2 v1 v0 vra : word),
  rw_cells rsegs m sp' (tk_fr (ws ++ tk_saved v11 v10 v9 v8 v7 v6 v5 v4 v3 v2 v1 v0 vra)) ->
  length ws = 15%nat -> nth 5 ws (Z_to_bv 64 0) = Z_to_bv 64 blp ->
  ExecF.rng RNG sp' TK_FRAME -> stk rsegs m lo sp' -> 0 <= sp' -> sp' + TK_FRAME < 2 ^ 63 ->
  ov_read_bytes rsegs m (wa (tk_sh TK_QD)) 1 = Some [Z_to_bv 8 0] ->
  ov_read_bytes rsegs m (wa (tk_sh blp)) 1 = Some [Z_to_bv 8 kbl] ->
  ExecF.rng RNG (tk_sh TK_QD) 1 -> ExecF.rng RNG (tk_sh blp) 1 ->
  ExecF.rng RNG TK_QD 4 -> ExecF.rng RNG blp 8 ->
  rw_cells rsegs m TK_QD [C4 (Z_to_bv 64 queued0)] ->
  (exists junk, rw_cells rsegs m blp [CB 8 junk]) ->
  (TK_QD + 4 <= sp' \/ sp' + TK_FRAME <= TK_QD) -> (blp + 8 <= sp' \/ sp' + TK_FRAME <= blp) ->
  (blp + 8 <= TK_QD \/ TK_QD + 4 <= blp) -> (tk_sh blp + 1 <= TK_QD \/ TK_QD + 4 <= tk_sh blp) ->
  kbl = 0 -> blp mod 8 = 0 -> 0 < blp -> blp + 8 < 2 ^ 63 ->
  0 <= taken <= 512 -> 0 <= kept <= 512 -> 0 <= len <= 1484 ->
  ExecF.evtF rsegs RNG
    (fun ms' => exists (m1 : word -> option byte) (spx r1 r2 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
       ms' = MS (mkR vra spx gp tp x5 x6 x7 v0 v1 (Z_to_bv 64 taken) r1 r2 x13 x14 x15 x16 x17
                     v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 x28 x29 x30 x31)
                F (ret_pc vra) fc None m1 (seg_rom rsegs) /\
       bv_unsigned spx = sp' + TK_FRAME /\
       munch [(TK_QD, TK_QD + 4); (blp, blp + 8)] m m1 /\ wmono rsegs m m1 /\
       stk rsegs m1 lo (sp' + TK_FRAME) /\
       rw_cells rsegs m1 TK_QD [C4 (Z_to_bv 64 kept)] /\
       rw_cells rsegs m1 blp [C8 (Z_to_bv 64 len)])
    (MS (mkR ra0 (Z_to_bv 64 sp') gp tp t0 t1 t2 s0 (Z_to_bv 64 TK_QD) a0 a1 a2 a3 a4 (Z_to_bv 64 taken)
             (Z_to_bv 64 len) (Z_to_bv 64 TK_K) s2 s3 s4 (Z_to_bv 64 kept) s6 s7 s8
             (Z_to_bv 64 (tk_sh TK_QD)) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 TK_X) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 t2 a0 a1 a2 a3 a4 t0 t1 s0 s2 s3 s4 s6 s7 s8 s10 s11 t3 t4 t5 t6 gp tp F fc m sp' lo taken kept
    len blp kbl queued0 ws v11 v10 v9 v8 v7 v6 v5 v4 v3 v2 v1 v0 vra FR LWS NTH RFR ST HS0 HS1 RSQ RSB GSQ GSB
    GQ GB CQ CB D1 D2 D3 D4 HKB HBM HB0 HB1 Ht Hk Hl.
  destruct (tk_len15 ws LWS) as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & ->).
  cbn [nth] in NTH. subst w5 kbl. destruct CB as [junk CB].
  cbn [tk_fr tk_saved map app] in FR.
  tk_lits.
  pose proof (munch_refl [(6176928, 6176928 + 4); (blp, blp + 8)] m) as MU.
  pose proof (munch_refl [(6176928, 6176928 + 4)] m) as MQ.
  pose proof (wmono_refl rsegs m) as WM.
  (* +0x3cc lb a0,0(s9): the shadow byte of s->queued; +0x3d0 bnez a0. The cell of s->queued is kept out of
     sight of the load: StepF's load reads an rw_cells fact at the literal distance of two literal addresses,
     which here is 2^31 cells. *)
  pose proof (tk_hid_intro _ CQ) as CQh. clear CQ.
  step. step. tk_br false ltac:(vm_compute; reflexivity).
  unfold tk_hid in CQh. rename CQh into CQ.
  (* +0x3d4 sw s5,0(s1): s->queued = kept *)
  step.
  (* +0x3d8 ld a0,0x28(sp): body_len; +0x3dc srli; +0x3e0 add; +0x3e4 lbu a1,0(a1): its shadow byte *)
  step. step. rewrite tk_shr3 by lia. step.
  tk_rd MQ RSB. clear MQ. step.
  (* +0x3e8 bnez a1 *)
  step. tk_br false ltac:(vm_compute; reflexivity).
  (* +0x3ec sd a6,0(a0): *body_len = len; +0x3f0 mv a0,a5 *)
  step. step.
  (* +0x3f4 .. +0x424: the saved registers back; +0x428 addi sp,sp,0xe0; +0x42c ret *)
  do 15 step.
  pose proof (tk_release _ _ _ _ ST FR) as ST'. cbn [cells_size csize Nat.add] in ST'.
  tk_post. split; [tk_ms|]. split; [rewrite unsigned_lit by lia; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact ST'|]. split; [exact CQ | exact CB].
Qed.
