(* take_seg_run: the footprint runs (lib/Lib/ExecF.v evtF, stepped with lib/Lib/StepF.v) of take in image B
   (fuzz_transport.asan-ubsan, entry 0x8a160 = transportb_sigma TB_take, 344 words; listing
   lib/B/Prog/DgnTransportBList.v from AF_take = 0x8ec0). The machine walk lib/B/Prog/take_cgW.v carries each of
   them into SRr with lib/B/Prog/DgnTransportBCgRun.v decode_run and cuts the four calls (three of __asan_memcpy, one
   of diginet_body_check) between them.

   The cuts (offsets from the entry):
     +0x000  TK_ENTRY  the prologue, the 4-byte store of 0 at has_display, s->queued;
             queued <> 0 goes to the loop head, queued = 0 to the exit;
     +0x12c  TK_L      the loop head of :358-382, turn i;
     +0x1b8  TK_CPY1   memcpy (body + len, c->bytes, c->len) (:365);
     +0x1bc  TK_R1     its return; then
     +0x1c8  TK_BCC    diginet_body_check (body, len + c->len) (:366);
     +0x1cc  TK_R2     its return: 0 takes the command (:368-371), anything else refuses;
     +0x268  TK_NF     the refusal (:373-375): kept = i skips the copy, else
     +0x294  TK_CPY2   memcpy (&s->queue[kept], c, 32) (:374), returning at
     +0x298  TK_R3;
     +0x2ac  TK_J      the end of a turn (:377): the break test, then the next turn, the tail or the exit;
     +0x388  TK_BRK    the break (:378): the tail loop or the exit;
     +0x3e0  TK_TL     the tail loop head, turn j;
     +0x404  TK_CPY3   memcpy (&s->queue[kept], &s->queue[j], 32), returning at
     +0x408  TK_R4;
     +0x44c  TK_X      the exit (:383-385): s->queued = kept, *body_len = len, return taken.

   The 256-byte frame holds len (sp + 0x88) and taken (sp + 0x90) through the whole loop; the registers hold
   i (s11), 32 i (s3), -i (s6), kept (s5) and ~(&s->queue[0]) (s0).

   Every instrumented check reads one shadow byte. For an access of n < 8 bytes at a the code goes on when the byte
   is 0, else when (a & 7) + n - 1 < byte (signed); for the 8-byte store at body_len any nonzero byte is the error
   path. The reads inside g_s's payload have a zero shadow byte (the walk gets that from the record); the two cells
   of the caller's frame (has_display, body_len) carry the shadow byte as a hypothesis khd / kbl with the
   disjunction the check needs.

   No error path is reached: each of the 17 calls of __asan_report_* sits behind a test these hypotheses decide;
   nor the UBSan trap word at +0x4c0: each of its 12 branches is decided by an alignment fact (hdp mod 4, blp mod 8,
   s mod 8), by the index bounds of the model (i, kept, j < 512), or by bp + 1484 <= 2^63 (~bp < len never holds).
   The register arithmetic of the ubsan code (not, subw of -i, sltiu / negw / and of the tail's mask) is
   lib/U/Prog/T/take_tail.v's. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import
  PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA AsanKAProof.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBSyms DgnTransportBAddr.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TWorldLemmas TSess0 TTake.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.

(* ---- the addresses: the entry is the listing's name, every interior point an offset ---- *)

Definition TK_ENTRY : Z := transportb_sigma TB_take.
Definition TK_AT (off : Z) : Z := TK_ENTRY + off.
Definition TK_L : Z := TK_AT 0x12c.
Definition TK_CPY1 : Z := TK_AT 0x1b8.
Definition TK_R1 : Z := TK_AT 0x1bc.
Definition TK_BCC : Z := TK_AT 0x1c8.
Definition TK_R2 : Z := TK_AT 0x1cc.
Definition TK_NF : Z := TK_AT 0x268.
Definition TK_CPY2 : Z := TK_AT 0x294.
Definition TK_R3 : Z := TK_AT 0x298.
Definition TK_J : Z := TK_AT 0x2ac.
Definition TK_BRK : Z := TK_AT 0x388.
Definition TK_TL : Z := TK_AT 0x3e0.
Definition TK_CPY3 : Z := TK_AT 0x404.
Definition TK_R4 : Z := TK_AT 0x408.
Definition TK_X : Z := TK_AT 0x44c.
Definition TK_MEMCPY : Z := transportb_sigma TB___asan_memcpy.
Definition TK_BC : Z := transportb_sigma TB_diginet_body_check.

(* g_s's base in image B and the fields the code addresses. *)
Definition TK_S : Z := TB_g_s.
Definition TK_MAXC : Z := TK_S + 52.
Definition TK_MAXB : Z := TK_S + 56.
Definition TK_Q0 : Z := TK_S + 1760.
Definition TK_QD : Z := TK_S + 18144.
Definition TK_K : Z := ASAN_K.
Definition tk_sh (a : Z) : Z := a / 8 + TK_K.
Definition TK_FRAME : Z := 256.
(* ~(&s->queue[0]), the bound of the UBSan pointer-overflow checks of &s->queue[q] (`not s0,a0` at +0x0e0). *)
Definition TK_NQ0 : Z := 18446744073709551615 - TK_Q0.

Lemma tk_addrs : TK_ENTRY = 0x8a160 /\ TK_S = 0x5df640 /\ TK_MAXC = 0x5df674 /\ TK_MAXB = 0x5df678 /\
  TK_Q0 = 0x5dfd20 /\ TK_QD = 0x5e3d20 /\ TK_S mod 64 = 0 /\ TK_MEMCPY = 0x523ec /\ TK_BC = 0x8c0fc.
Proof.
  repeat split; vm_compute; reflexivity.
Qed.

(* The 256-byte frame as 32 8-byte cells: offsets 0 .. 0xf8. Slots 0 .. 0x90 are the function's spills (slot 0
   is never written), slots 0x98 .. 0xf8 the saved s11 .. s0 and ra. *)
Definition tk_fr (ws : list word) : list cell := map C8 ws.

(* The spills of the loop: 0x08 / 0x10 (a & 7) + 3 of max_body and max_cmds, 0x18 has_display, 0x20 its shadow byte
   address, 0x28 the shadow byte address of s->queued, 0x30 ~body, 0x38 body_len, 0x40 s, 0x48 allow_display,
   0x50 body, 0x58 / 0x60 the shadow byte addresses of max_body and max_cmds, 0x68 &max_body, 0x70 the shadow base,
   0x78 &s->queue[0], 0x80 &s->queued, 0x88 len, 0x90 taken. *)
Definition tk_spill (bp blp hdp allow len taken : Z) (j00 : word) : list word :=
  [j00; Z_to_bv 64 3; Z_to_bv 64 7; Z_to_bv 64 hdp; Z_to_bv 64 (tk_sh hdp); Z_to_bv 64 (tk_sh TK_QD);
   Z_to_bv 64 (18446744073709551615 - bp); Z_to_bv 64 blp; Z_to_bv 64 TK_S; Z_to_bv 64 allow; Z_to_bv 64 bp;
   Z_to_bv 64 (tk_sh TK_MAXB); Z_to_bv 64 (tk_sh TK_MAXC); Z_to_bv 64 TK_MAXB; Z_to_bv 64 TK_K;
   Z_to_bv 64 TK_Q0; Z_to_bv 64 TK_QD; Z_to_bv 64 len; Z_to_bv 64 taken].

Definition tk_saved (v11 v10 v9 v8 v7 v6 v5 v4 v3 v2 v1 v0 vra : word) : list word :=
  [v11; v10; v9; v8; v7; v6; v5; v4; v3; v2; v1; v0; vra].

(* The spill words the exit reads: body_len (0x38), the shadow base (0x70), len (0x88), taken (0x90). The path with
   s->queued = 0 writes only those four (and 0x20, 0x48, 0x50) before the exit. *)
Definition tk_xfr (ws : list word) (blp len taken : Z) : Prop :=
  length ws = 19%nat /\ nth 7 ws (Z_to_bv 64 0) = Z_to_bv 64 blp /\ nth 14 ws (Z_to_bv 64 0) = Z_to_bv 64 TK_K /\
  nth 17 ws (Z_to_bv 64 0) = Z_to_bv 64 len /\ nth 18 ws (Z_to_bv 64 0) = Z_to_bv 64 taken.

Lemma tk_xfr_spill : forall bp blp hdp allow len taken j00,
  tk_xfr (tk_spill bp blp hdp allow len taken j00) blp len taken.
Proof. intros. unfold tk_xfr, tk_spill. cbn [length nth]. repeat split; reflexivity. Qed.

(* ---- the register arithmetic of the ubsan code (lib/U/Prog/T/take_tail.v's lemmas) ---- *)

(* not of a register (the pointer-overflow bounds ~bp and ~&s->queue[0]) *)
Lemma tk_not : forall x, 0 <= x < 2 ^ 64 ->
  Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 x)) 18446744073709551615) = Z_to_bv 64 (18446744073709551615 - x).
Proof. intros x Hx. rewrite unsigned_lit by lia. rewrite zb_lxor_ones by lia. reflexivity. Qed.

(* the alignment checks: andi of an aligned pointer *)
Lemma tk_land3 : forall t, 0 <= t < 2 ^ 64 -> t mod 4 = 0 -> Z.land (bv_unsigned (Z_to_bv 64 t)) 3 = 0.
Proof. intros t Ht H4. rewrite unsigned_lit by lia. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. exact H4. Qed.

Lemma tk_land7 : forall t, 0 <= t < 2 ^ 64 -> t mod 8 = 0 -> Z.land (bv_unsigned (Z_to_bv 64 t)) 7 = 0.
Proof. intros t Ht H8. rewrite unsigned_lit by lia. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. exact H8. Qed.

(* subw / negw of the register s6 = -i (the loop counts i down in s6) *)
Lemma tk_swrap_sub_neg : forall a i, bv_swrap 32 (a - bv_unsigned (Z_to_bv 64 (- i))) = bv_swrap 32 (a + i).
Proof.
  intros a i. rewrite unsigned_lit_wrap. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  f_equal. rewrite (Z.mod_eq (- i) (2 ^ 64)) by lia.
  replace (a - (- i - 2 ^ 64 * (- i / 2 ^ 64)) + 2 ^ 31)
    with ((a + i + 2 ^ 31) + (2 ^ 32 * (- i / 2 ^ 64)) * 2 ^ 32) by lia.
  apply Z_mod_plus_full.
Qed.

(* the mask of the tail's index check: sltiu a1,a0,514 with a0 = 513 - kept *)
Lemma tk_sltiu1 : forall x, 0 <= x < 514 -> v_sltiu (Z_to_bv 64 x) 514 = Z_to_bv 64 1.
Proof.
  intros x Hx. unfold v_sltiu. rewrite unsigned_lit by lia. change (bv_wrap 64 514) with 514.
  replace (x <? 514) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

(* and of the mask -1 (the step folds bv_unsigned of the closed -1) *)
Lemma tk_land_m1 : forall x, 0 <= x < 2 ^ 64 ->
  Z.land 18446744073709551615 (bv_unsigned (Z_to_bv 64 x)) = x.
Proof.
  intros x Hx. rewrite (unsigned_lit x) by lia. change 18446744073709551615 with (Z.ones 64).
  rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

(* ---- the proof kit of the runs ---- *)

(* Every address constant of the runs as its literal (StepF's step reads literal pcs; the arithmetic of the address
   registers folds on literals). *)
Ltac tk_lit c := let v := eval vm_compute in c in try change c with v in *.
Ltac tk_lits :=
  tk_lit TK_L; tk_lit TK_CPY1; tk_lit TK_R1; tk_lit TK_BCC; tk_lit TK_R2; tk_lit TK_NF; tk_lit TK_CPY2;
  tk_lit TK_R3; tk_lit TK_J; tk_lit TK_BRK; tk_lit TK_TL; tk_lit TK_CPY3; tk_lit TK_R4; tk_lit TK_X;
  tk_lit TK_MEMCPY; tk_lit TK_BC; tk_lit TK_ENTRY; tk_lit TK_NQ0;
  tk_lit (tk_sh TK_MAXC); tk_lit (tk_sh TK_MAXB); tk_lit (tk_sh TK_QD);
  tk_lit TK_MAXC; tk_lit TK_MAXB; tk_lit TK_Q0; tk_lit TK_QD; tk_lit TK_S; tk_lit TK_FRAME;
  unfold tk_sh in *; tk_lit TK_K.

(* A branch decided to b. *)
Ltac tk_br b tac := lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b; [cbv iota | symmetry; tac]
  end.

(* Two words given by values equal modulo 2^64. *)
Lemma tk_bv_mod : forall a b, a mod 2 ^ 64 = b mod 2 ^ 64 -> Z_to_bv 64 a = Z_to_bv 64 b.
Proof. intros a b H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. exact H. Qed.

(* The two machine states agree register by register (the arithmetic of a register by lia); the stepped state's
   registers are a TNode tree, so the post's mkR is unfolded too. *)
Ltac tk_tree :=
  first [ reflexivity
        | lazymatch goal with
          | |- TNode _ _ _ = TNode _ _ _ => f_equal; tk_tree
          | |- Some _ = Some _ => f_equal; tk_tree
          | |- Z_to_bv 64 _ = Z_to_bv 64 _ =>
              first [ f_equal; lia
                    | apply tk_bv_mod; rewrite ?unsigned_lit_wrap; Z.div_mod_to_equations; lia ]
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

Lemma tk_len32 : forall (ws : list word), length ws = 32%nat ->
  exists w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27
         w28 w29 w30 w31,
    ws = [w0; w1; w2; w3; w4; w5; w6; w7; w8; w9; w10; w11; w12; w13; w14; w15; w16; w17; w18; w19; w20; w21;
          w22; w23; w24; w25; w26; w27; w28; w29; w30; w31].
Proof.
  intros ws L.
  do 32 (destruct ws as [|? ws]; [discriminate L|]). destruct ws; [|discriminate L].
  do 32 eexists. reflexivity.
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

(* The 13 saved words of the frame, one by one, and the 19 spill words. *)
Lemma tk_len13 : forall (sv : list word), length sv = 13%nat ->
  exists v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12, sv = [v0; v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11; v12].
Proof.
  intros sv L.
  do 13 (destruct sv as [|? sv]; [discriminate L|]). destruct sv; [|discriminate L].
  do 13 eexists. reflexivity.
Qed.

Lemma tk_len19 : forall (ws : list word), length ws = 19%nat ->
  exists w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18,
    ws = [w0; w1; w2; w3; w4; w5; w6; w7; w8; w9; w10; w11; w12; w13; w14; w15; w16; w17; w18].
Proof.
  intros ws L.
  do 19 (destruct ws as [|? ws]; [discriminate L|]). destruct ws; [|discriminate L].
  do 19 eexists. reflexivity.
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

(* The test of has_display's shadow byte khd at the prologue (`lb` then `bnez`): 0, or above hdp mod 8 + 3 (the
   slow path +0x4c4 .. +0x4cc: andi with 7, addi 3, blt back to +0x070). *)
Local Ltac tk_khd HK khd hdp :=
  destruct HK as [K0|[K1 K2]];
  [ subst khd; tk_br false ltac:(vm_compute; reflexivity)
  | tk_br true ltac:(rewrite sxb_eq0, tk_signed8 by lia; tk_zc);
    step; step; step;
    tk_br true ltac:(rewrite (unsigned_lit hdp), land7 by lia; rewrite lts_low by lia;
                     rewrite tk_signed8 by lia; tk_zc) ].

(* The prologue of take up to the test of s->queued (+0x000 .. +0x0a4): the frame and the 15 stores of the saved
   registers, allow_display and body; the UBSan alignment check of has_display; the shadow base through its GOT
   word; the instrumented 4-byte store of 0 at has_display; the UBSan alignment check of s; the instrumented load
   of s->queued. MF is the munch fact of the frame alone, MU that of the frame and has_display. *)
Local Ltac tk_pro MF MU RGC RCK RSH RSQ RQ HK khd hdp :=
  (* +0x000 addi sp,sp,-256; +0x004 .. +0x034 sd ra, s0 .. s11; +0x038 sd a3,0x48(sp); +0x03c sd a1,0x50(sp) *)
  do 16 step;
  (* +0x040 andi a1,a4,3; +0x044 bnez a1 (to the trap): hdp mod 4 = 0 *)
  step; rewrite (tk_land3 hdp) by lia; step; tk_br false ltac:(vm_compute; reflexivity);
  (* +0x048 mv a3,a0; +0x04c auipc a0; +0x050 ld a0: GOT_CELL_K; +0x054 ld a1,0(a0): the shadow base *)
  step; step; tk_rd MF RGC; step; tk_rd MF RCK; step;
  (* +0x058 srli a0,a4,3; +0x05c sd a1,0x70(sp); +0x060 add a0,a0,a1; +0x064 sd a0,0x20(sp) *)
  step; rewrite tk_shr3 by lia; step; step; step;
  (* +0x068 lb a0,0(a0): the shadow byte of has_display; +0x06c bnez a0 *)
  tk_rd MF RSH; step; step;
  tk_khd HK khd hdp; clear MF;
  (* +0x070 andi a0,a3,7: s & 7 = 0; +0x074 sw zero,0(a4); +0x078 bnez a0 (to the trap) *)
  step; step; step; tk_br false ltac:(vm_compute; reflexivity);
  (* +0x07c lui a0,4; +0x080 addiw a0,a0,0x6e0; +0x084 add a5,a3,a0: &s->queued; +0x088 srli a0,a5,3;
     +0x08c ld a1,0x70(sp); +0x090 add s8,a0,a1: its shadow byte address *)
  do 6 step;
  (* +0x094 lb a0,0(s8); +0x098 bnez a0 *)
  tk_rd MU RSQ; step; step; tk_br false ltac:(vm_compute; reflexivity);
  (* +0x09c sd a2,0x38(sp); +0x0a0 lw a0,0(a5): s->queued; +0x0a4 beqz a0 *)
  step; tk_rd MU RQ; step; rewrite tk_lw_put, tk_s32_small by lia; step.

(* ---- run 1: the prologue, s->queued <> 0, to the loop head ---- *)

(* The machine state at TK_L with the turn i of take_loop_m still to run (len and taken are in the frame): the
   free registers are ra, t1, t2, s1, a0 .. a4, s4, s9, s10, t3 .. t6. *)
Definition tk_at_L (ra t1 t2 s1 a0 a1 a2 a3 a4 s4 s9 s10 t3 t4 t5 t6 : word) (gp tp : word) (F : bvmap 5 word)
    (fc : bv 32) (m : word -> option byte) (sp' i kept : Z) : machine_state :=
  MS (mkR ra (Z_to_bv 64 sp') gp tp (Z_to_bv 64 (tk_sh TK_MAXB)) t1 t2 (Z_to_bv 64 TK_NQ0) s1 a0 a1 a2 a3 a4
          (Z_to_bv 64 TK_QD) (Z_to_bv 64 TK_MAXB) (Z_to_bv 64 (tk_sh TK_MAXC)) (Z_to_bv 64 TK_S)
          (Z_to_bv 64 (32 * i)) s4 (Z_to_bv 64 kept) (Z_to_bv 64 (- i)) (Z_to_bv 64 TK_MAXC)
          (Z_to_bv 64 (tk_sh TK_QD)) s9 s10 (Z_to_bv 64 i) t3 t4 t5 t6)
     F (Z_to_bv 64 TK_L) fc None m (seg_rom rsegs).

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
    (fun ms' => exists (m1 : word -> option byte) (x10 x11 x12 x13 x14 j00 : word),
       ms' = tk_at_L ra t1 t2 s1 x10 x11 x12 x13 x14 s4 s9 s10 t3 t4 t5 t6 gp tp F fc m1
               (bv_unsigned sp - TK_FRAME) 0 0 /\
       munch [(bv_unsigned sp - TK_FRAME, bv_unsigned sp); (hdp, hdp + 4)] m m1 /\ wmono rsegs m m1 /\
       stk rsegs m1 lo (bv_unsigned sp - TK_FRAME) /\
       rw_cells rsegs m1 hdp [C4 (Z_to_bv 64 0)] /\
       rw_cells rsegs m1 (bv_unsigned sp - TK_FRAME)
         (tk_fr (tk_spill bp blp hdp allow 0 0 j00 ++ tk_saved s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)))
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
  unfold tk_at_L. cbn [tk_fr tk_spill tk_saved map app].
  tk_lits.
  pose proof (munch_refl [(bv_unsigned sp - 256, bv_unsigned sp); (hdp, hdp + 4)] m) as MU.
  pose proof (munch_refl [(bv_unsigned sp - 256, bv_unsigned sp)] m) as MF.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 256%nat ST.
  destruct (tk_c8s 32 _ _ _ FR) as (ws & LW & FR'). clear FR.
  destruct (tk_len32 ws LW) as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 &
    w15 & w16 & w17 & w18 & w19 & w20 & w21 & w22 & w23 & w24 & w25 & w26 & w27 & w28 & w29 & w30 & w31 & ->).
  cbn [map] in FR'. rename FR' into FR.
  tk_pro MF MU RGC RCK RSH RSQ RQ HK khd hdp.
  all: tk_br false tk_cmp.
  (* +0x0a8 .. +0x0d0: the spill of has_display, the counters (len and taken in the frame), the cfg addresses,
     body back *)
  all: do 11 step.
  (* +0x0d4 not a1,a1: ~body *)
  all: step; rewrite ?tk_not by lia.
  (* +0x0d8 sd a1,0x30(sp); +0x0dc sd a0,0x78(sp); +0x0e0 not s0,a0: ~(&s->queue[0]) *)
  all: step; step; step; rewrite ?tk_not by lia.
  (* +0x0e4 .. +0x128: s, the shadow byte addresses and (a & 7) + 3 of the cfg fields, the spills of the loop *)
  all: do 18 step.
  all: tk_post; split; [tk_ms|]; split; [exact MU|]; split; [exact WM|]; split; [exact ST|]; split; [exact CH|].
  all: exact FR.
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
    (fun ms' => exists (m1 : word -> option byte) (x10 x11 x12 x13 x14 : word) (ws : list word),
       ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - TK_FRAME)) gp tp t0 t1 t2 s0 s1 x10 x11 x12 x13 x14
                     (Z_to_bv 64 TK_QD) a6 a7 s2 s3 s4 (Z_to_bv 64 0) s6 s7 (Z_to_bv 64 (tk_sh TK_QD))
                     s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 TK_X) fc None m1 (seg_rom rsegs) /\
       munch [(bv_unsigned sp - TK_FRAME, bv_unsigned sp); (hdp, hdp + 4)] m m1 /\ wmono rsegs m m1 /\
       stk rsegs m1 lo (bv_unsigned sp - TK_FRAME) /\
       rw_cells rsegs m1 hdp [C4 (Z_to_bv 64 0)] /\
       tk_xfr ws blp 0 0 /\
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
  pose proof (munch_refl [(bv_unsigned sp - 256, bv_unsigned sp); (hdp, hdp + 4)] m) as MU.
  pose proof (munch_refl [(bv_unsigned sp - 256, bv_unsigned sp)] m) as MF.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 256%nat ST.
  destruct (tk_c8s 32 _ _ _ FR) as (ws & LW & FR'). clear FR.
  destruct (tk_len32 ws LW) as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 &
    w15 & w16 & w17 & w18 & w19 & w20 & w21 & w22 & w23 & w24 & w25 & w26 & w27 & w28 & w29 & w30 & w31 & ->).
  cbn [map] in FR'. rename FR' into FR.
  tk_pro MF MU RGC RCK RSH RSQ RQ HK khd hdp.
  all: tk_br true ltac:(vm_compute; reflexivity).
  (* +0x440 mv s5,zero; +0x444 sd zero,0x88(sp); +0x448 sd zero,0x90(sp) *)
  all: do 3 step.
  all: apply evtF_done; cbv beta; do 6 eexists;
    exists [w0; w1; w2; w3; Z_to_bv 64 (hdp / 8 + 2147450880); w5; w6; Z_to_bv 64 blp; w8; Z_to_bv 64 allow;
            Z_to_bv 64 bp; w11; w12; w13; Z_to_bv 64 2147450880; w15; w16; Z_to_bv 64 0; Z_to_bv 64 0].
  all: split; [tk_ms|]; split; [exact MU|]; split; [exact WM|]; split; [exact ST|]; split; [exact CH|].
  all: split; [unfold tk_xfr; cbn [length nth]; repeat split; reflexivity|].
  all: cbn [tk_fr tk_saved map app]; exact FR.
Qed.

(* ---- the states of the loop ---- *)

(* The state at TK_NF (the refusal), TK_J (the end of a turn) and TK_BRK (the break): s4 = &s->queue[i] - 1760,
   s9 = &s->queue[i]; the free registers are ra, t1, t2, s1, a0 .. a4, s10, t3 .. t6. *)
Definition tk_at (pc : Z) (ra t1 t2 s1 a0 a1 a2 a3 a4 s10 t3 t4 t5 t6 : word) (gp tp : word) (F : bvmap 5 word)
    (fc : bv 32) (m : word -> option byte) (sp' i kept : Z) : machine_state :=
  MS (mkR ra (Z_to_bv 64 sp') gp tp (Z_to_bv 64 (tk_sh TK_MAXB)) t1 t2 (Z_to_bv 64 TK_NQ0) s1 a0 a1 a2 a3 a4
          (Z_to_bv 64 TK_QD) (Z_to_bv 64 TK_MAXB) (Z_to_bv 64 (tk_sh TK_MAXC)) (Z_to_bv 64 TK_S)
          (Z_to_bv 64 (32 * i)) (Z_to_bv 64 (TK_S + 32 * i)) (Z_to_bv 64 kept) (Z_to_bv 64 (- i))
          (Z_to_bv 64 TK_MAXC) (Z_to_bv 64 (tk_sh TK_QD)) (Z_to_bv 64 (TK_Q0 + 32 * i)) s10 (Z_to_bv 64 i)
          t3 t4 t5 t6)
     F (Z_to_bv 64 pc) fc None m (seg_rom rsegs).

(* ---- runs from the loop head ---- *)

(* The reads of turn i that every path makes: the two shadow bytes of the cfg fields, the shadow bytes of
   c->len and c->display, the two cfg fields, c->len and c->display. All lie in g_s's payload, so their shadow
   bytes are 0. *)
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

(* +0x12c .. +0x150: the two UBSan checks of &s->queue[i] (i = 513, &s->queue[0] + 32 i wrapping), the shadow
   check of max_cmds, max_cmds, s4 / s9, taken back from the frame. *)
Local Ltac tk_l1 :=
  step; step; tk_br false tk_cmp; step; tk_br false tk_cmp;
  step; step; tk_br false ltac:(vm_compute; reflexivity);
  step; rewrite tk_lw_put; step; step; step.

(* +0x154 .. +0x184: c->len's address and shadow byte address, its shadow check, the shadow check of max_body,
   c->len, max_body, len back from the frame, len + c->len. *)
Local Ltac tk_l2 i :=
  step; replace (6157888 + 32 * i + 1784) with (6159648 + 32 * i + 24) by lia;
  step; rewrite tk_shr3 by lia; step; step;
  step; step; tk_br false ltac:(vm_compute; reflexivity);
  step; step; rewrite tk_lbu_put by lia; step; tk_br false ltac:(vm_compute; reflexivity);
  step; rewrite tk_lwu_put by lia; step; step; step.

(* +0x248 .. +0x264 (allow_display = 0): c->display under its shadow check, then its test. *)
Local Ltac tk_disp i :=
  step; replace (6157888 + 32 * i + 1785) with (6159648 + 32 * i + 25) by lia;
  step; rewrite tk_shr3 by lia; step; step;
  step; step; tk_br false ltac:(vm_compute; reflexivity);
  step; rewrite tk_lbu_put by lia; step.

(* +0x190 .. +0x1b8 of a turn that fits: the UBSan check of body + len (~body < len), c->len under its shadow
   check, len and body into s8 and s2, the call. *)
Local Ltac tk_fit_tail :=
  step; step; step; tk_br false tk_cmp;
  step; step; tk_br false ltac:(vm_compute; reflexivity);
  step; rewrite tk_lbu_put by lia; step; step; step; step; step.

(* The turn fits the counters and the pacing: the walk reaches the copy of :365. *)
Lemma tk_run_fit : forall (RNG : ExecF.footprint)
    (ra t1 t2 s1 a0 a1 a2 a3 a4 s4 s9 s10 t3 t4 t5 t6 : word) (gp tp : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (sp' i taken kept len clen disp maxc maxb bp blp hdp allow : Z) (j00 : word)
    (sv : list word),
  tk_rd_turn m i clen disp maxc maxb -> tk_rng_turn RNG i ->
  tk_bounds i taken kept len clen disp maxc maxb ->
  rw_cells rsegs m sp' (tk_fr (tk_spill bp blp hdp allow len taken j00 ++ sv)) -> length sv = 13%nat ->
  ExecF.rng RNG sp' TK_FRAME -> 0 <= sp' -> sp' + TK_FRAME < 2 ^ 63 ->
  0 < bp -> bp + 1484 < 2 ^ 63 -> - 2 ^ 31 <= allow < 2 ^ 31 ->
  taken < maxc -> len + clen <= maxb -> (allow <> 0 \/ disp = 0) ->
  ExecF.evtF rsegs RNG
    (fun ms' =>
       ms' = MS (mkR (Z_to_bv 64 TK_R1) (Z_to_bv 64 sp') gp tp (Z_to_bv 64 (tk_sh TK_MAXB)) t1 t2
                     (Z_to_bv 64 TK_NQ0) (Z_to_bv 64 (tk_sh (TK_Q0 + 32 * i + 24))) (Z_to_bv 64 (bp + len))
                     (Z_to_bv 64 (TK_Q0 + 32 * i)) (Z_to_bv 64 clen) a3 a4 (Z_to_bv 64 TK_QD)
                     (Z_to_bv 64 TK_MAXB) (Z_to_bv 64 (tk_sh TK_MAXC)) (Z_to_bv 64 bp) (Z_to_bv 64 (32 * i))
                     (Z_to_bv 64 (TK_S + 32 * i)) (Z_to_bv 64 kept) (Z_to_bv 64 (- i)) (Z_to_bv 64 TK_MAXC)
                     (Z_to_bv 64 len) (Z_to_bv 64 (TK_Q0 + 32 * i)) (Z_to_bv 64 (TK_Q0 + 32 * i + 24))
                     (Z_to_bv 64 i) t3 t4 t5 t6)
                F (Z_to_bv 64 TK_MEMCPY) fc None m (seg_rom rsegs))
    (tk_at_L ra t1 t2 s1 a0 a1 a2 a3 a4 s4 s9 s10 t3 t4 t5 t6 gp tp F fc m sp' i kept).
Proof.
  intros RNG ra t1 t2 s1 a0 a1 a2 a3 a4 s4 s9 s10 t3 t4 t5 t6 gp tp F fc m sp' i taken kept len clen disp maxc maxb
    bp blp hdp allow j00 sv RD RG BD FR LSV RFR HS0 HS1 HB0 HB1 HAL HC HB HAD.
  destruct RD as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8).
  destruct RG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
  destruct BD as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
  cbn [tk_fr tk_spill map app] in FR.
  unfold tk_at_L. tk_lits.
  tk_l1.
  (* +0x150 bgeu a1,a0: taken < max_cmds *)
  step. tk_br false tk_cmp.
  tk_l2 i.
  (* +0x184 bltu a1,a0: len + c->len <= max_body *)
  tk_br false tk_cmp.
  (* +0x188 ld a0,0x48(sp): allow_display; +0x18c beqz a0 *)
  step. step.
  destruct (Z.eq_dec allow 0) as [HA|HA].
  - (* allow_display = 0, so c->display = 0: +0x248 .. +0x264, back to +0x190 *)
    assert (HD : disp = 0) by (destruct HAD; [contradiction | exact H]).
    subst allow disp. tk_br true ltac:(vm_compute; reflexivity).
    tk_disp i. tk_br true ltac:(vm_compute; reflexivity).
    tk_fit_tail.
    tk_post. tk_ms.
  - tk_br false tk_cmp.
    tk_fit_tail.
    tk_post. tk_ms.
Qed.

(* The turn does not fit: taken reached max_cmds (:360). *)
Lemma tk_run_nofit_a : forall (RNG : ExecF.footprint)
    (ra t1 t2 s1 a0 a1 a2 a3 a4 s4 s9 s10 t3 t4 t5 t6 : word) (gp tp : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (sp' i taken kept len clen disp maxc maxb bp blp hdp allow : Z) (j00 : word)
    (sv : list word),
  tk_rd_turn m i clen disp maxc maxb -> tk_rng_turn RNG i ->
  tk_bounds i taken kept len clen disp maxc maxb ->
  rw_cells rsegs m sp' (tk_fr (tk_spill bp blp hdp allow len taken j00 ++ sv)) -> length sv = 13%nat ->
  ExecF.rng RNG sp' TK_FRAME -> 0 <= sp' -> sp' + TK_FRAME < 2 ^ 63 ->
  maxc <= taken ->
  ExecF.evtF rsegs RNG
    (fun ms' => exists (z0 z1 : word),
       ms' = tk_at TK_NF ra t1 t2 s1 z0 z1 a2 a3 a4 s10 t3 t4 t5 t6 gp tp F fc m sp' i kept)
    (tk_at_L ra t1 t2 s1 a0 a1 a2 a3 a4 s4 s9 s10 t3 t4 t5 t6 gp tp F fc m sp' i kept).
Proof.
  intros RNG ra t1 t2 s1 a0 a1 a2 a3 a4 s4 s9 s10 t3 t4 t5 t6 gp tp F fc m sp' i taken kept len clen disp maxc maxb
    bp blp hdp allow j00 sv RD RG BD FR LSV RFR HS0 HS1 HC.
  destruct RD as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8).
  destruct RG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
  destruct BD as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
  cbn [tk_fr tk_spill map app] in FR.
  unfold tk_at_L, tk_at. tk_lits.
  tk_l1.
  (* +0x150 bgeu a1,a0: max_cmds <= taken *)
  step. tk_br true tk_cmp.
  tk_post. tk_ms.
Qed.

(* The turn does not fit: len + c->len passes max_body (:361). *)
Lemma tk_run_nofit_b : forall (RNG : ExecF.footprint)
    (ra t1 t2 s1 a0 a1 a2 a3 a4 s4 s9 s10 t3 t4 t5 t6 : word) (gp tp : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (sp' i taken kept len clen disp maxc maxb bp blp hdp allow : Z) (j00 : word)
    (sv : list word),
  tk_rd_turn m i clen disp maxc maxb -> tk_rng_turn RNG i ->
  tk_bounds i taken kept len clen disp maxc maxb ->
  rw_cells rsegs m sp' (tk_fr (tk_spill bp blp hdp allow len taken j00 ++ sv)) -> length sv = 13%nat ->
  ExecF.rng RNG sp' TK_FRAME -> 0 <= sp' -> sp' + TK_FRAME < 2 ^ 63 ->
  taken < maxc -> maxb < len + clen ->
  ExecF.evtF rsegs RNG
    (fun ms' => exists (z9 z0 z1 z2 z26 : word),
       ms' = tk_at TK_NF ra t1 t2 z9 z0 z1 z2 a3 a4 z26 t3 t4 t5 t6 gp tp F fc m sp' i kept)
    (tk_at_L ra t1 t2 s1 a0 a1 a2 a3 a4 s4 s9 s10 t3 t4 t5 t6 gp tp F fc m sp' i kept).
Proof.
  intros RNG ra t1 t2 s1 a0 a1 a2 a3 a4 s4 s9 s10 t3 t4 t5 t6 gp tp F fc m sp' i taken kept len clen disp maxc maxb
    bp blp hdp allow j00 sv RD RG BD FR LSV RFR HS0 HS1 HC HB.
  destruct RD as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8).
  destruct RG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
  destruct BD as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
  cbn [tk_fr tk_spill map app] in FR.
  unfold tk_at_L, tk_at. tk_lits.
  tk_l1.
  step. tk_br false tk_cmp.
  tk_l2 i.
  (* +0x184 bltu a1,a0: max_body < len + c->len *)
  tk_br true tk_cmp.
  tk_post. tk_ms.
Qed.

(* The turn does not fit: the pacing (:362), allow_display = 0 and c->display <> 0. *)
Lemma tk_run_nofit_c : forall (RNG : ExecF.footprint)
    (ra t1 t2 s1 a0 a1 a2 a3 a4 s4 s9 s10 t3 t4 t5 t6 : word) (gp tp : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (sp' i taken kept len clen disp maxc maxb bp blp hdp allow : Z) (j00 : word)
    (sv : list word),
  tk_rd_turn m i clen disp maxc maxb -> tk_rng_turn RNG i ->
  tk_bounds i taken kept len clen disp maxc maxb ->
  rw_cells rsegs m sp' (tk_fr (tk_spill bp blp hdp allow len taken j00 ++ sv)) -> length sv = 13%nat ->
  ExecF.rng RNG sp' TK_FRAME -> 0 <= sp' -> sp' + TK_FRAME < 2 ^ 63 ->
  taken < maxc -> len + clen <= maxb -> allow = 0 -> disp <> 0 ->
  ExecF.evtF rsegs RNG
    (fun ms' => exists (z9 z0 z1 z2 z26 : word),
       ms' = tk_at TK_NF ra t1 t2 z9 z0 z1 z2 a3 a4 z26 t3 t4 t5 t6 gp tp F fc m sp' i kept)
    (tk_at_L ra t1 t2 s1 a0 a1 a2 a3 a4 s4 s9 s10 t3 t4 t5 t6 gp tp F fc m sp' i kept).
Proof.
  intros RNG ra t1 t2 s1 a0 a1 a2 a3 a4 s4 s9 s10 t3 t4 t5 t6 gp tp F fc m sp' i taken kept len clen disp maxc maxb
    bp blp hdp allow j00 sv RD RG BD FR LSV RFR HS0 HS1 HC HB HA HD.
  subst allow.
  destruct RD as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8).
  destruct RG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
  destruct BD as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
  cbn [tk_fr tk_spill map app] in FR.
  unfold tk_at_L, tk_at. tk_lits.
  tk_l1.
  step. tk_br false tk_cmp.
  tk_l2 i.
  tk_br false tk_cmp.
  (* +0x188 ld a0,0x48(sp): allow_display = 0; +0x18c beqz a0 *)
  step. step. tk_br true ltac:(vm_compute; reflexivity).
  (* +0x248 .. +0x264: c->display <> 0, so on to +0x268 *)
  tk_disp i. tk_br false tk_cmp.
  tk_post. tk_ms.
Qed.

(* ---- the return of the copy of :365, to the call of diginet_body_check ---- *)

(* The state at TK_R1 / TK_R2: the callee kept s0 .. s11, sp, gp and tp. *)
Definition tk_at_R (pc : Z) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (gp tp : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (sp' i kept len bp : Z) : machine_state :=
  MS (mkR ra (Z_to_bv 64 sp') gp tp t0 t1 t2 (Z_to_bv 64 TK_NQ0) (Z_to_bv 64 (tk_sh (TK_Q0 + 32 * i + 24)))
          a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 bp) (Z_to_bv 64 (32 * i)) (Z_to_bv 64 (TK_S + 32 * i))
          (Z_to_bv 64 kept) (Z_to_bv 64 (- i)) (Z_to_bv 64 TK_MAXC) (Z_to_bv 64 len) (Z_to_bv 64 (TK_Q0 + 32 * i))
          (Z_to_bv 64 (TK_Q0 + 32 * i + 24)) (Z_to_bv 64 i) t3 t4 t5 t6)
     F (Z_to_bv 64 pc) fc None m (seg_rom rsegs).

Lemma tk_run_bc_call : forall (RNG : ExecF.footprint)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (gp tp : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (sp' i kept len clen bp : Z),
  ov_read_bytes rsegs m (wa (TK_Q0 + 32 * i + 24)) 1 = Some (TW.put 1 clen) ->
  ExecF.rng RNG (TK_Q0 + 32 * i + 24) 1 ->
  0 <= i < 512 -> 0 <= clen < 256 -> 0 <= len <= 1484 -> 0 < bp -> bp + 1484 < 2 ^ 63 ->
  ExecF.evtF rsegs RNG
    (fun ms' =>
       ms' = tk_at_R TK_BC (Z_to_bv 64 TK_R2) t0 t1 t2 (Z_to_bv 64 bp) (Z_to_bv 64 (len + clen)) a2 a3 a4 a5 a6 a7
               t3 t4 t5 t6 gp tp F fc m sp' i kept len bp)
    (tk_at_R TK_R1 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 gp tp F fc m sp' i kept len bp).
Proof.
  intros RNG ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 gp tp F fc m sp' i kept len clen bp
    RC GC Hi Hc Hl Hb0 Hb1.
  unfold tk_at_R. tk_lits.
  (* +0x1bc lbu a1,0x6f8(s4): c->len; +0x1c0 add a1,s8,a1; +0x1c4 mv a0,s2; +0x1c8 the call *)
  step. rewrite tk_lbu_put by lia. step. step. step.
  tk_post. tk_ms.
Qed.

(* ---- the return of diginet_body_check ---- *)

(* diginet_body_check refused the joined body: the turn refuses too (:366). *)
Lemma tk_run_bc_ne : forall (RNG : ExecF.footprint)
    (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (gp tp : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (sp' i taken kept len bp blp hdp allow res : Z) (j00 : word) (sv : list word),
  rw_cells rsegs m sp' (tk_fr (tk_spill bp blp hdp allow len taken j00 ++ sv)) -> length sv = 13%nat ->
  ExecF.rng RNG sp' TK_FRAME -> 0 <= sp' -> sp' + TK_FRAME < 2 ^ 63 ->
  0 <= i < 512 -> res <> 0 -> - 2 ^ 31 <= res < 2 ^ 31 ->
  ExecF.evtF rsegs RNG
    (fun ms' => exists (z9 z26 : word),
       ms' = tk_at TK_NF ra t1 t2 z9 (Z_to_bv 64 res) a1 a2 a3 a4 z26 t3 t4 t5 t6 gp tp F fc m sp' i kept)
    (tk_at_R TK_R2 ra t0 t1 t2 (Z_to_bv 64 res) a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 gp tp F fc m sp' i kept len bp).
Proof.
  intros RNG ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 gp tp F fc m sp' i taken kept len bp blp hdp allow
    res j00 sv FR LSV RFR HS0 HS1 Hi HR HRr.
  cbn [tk_fr tk_spill map app] in FR.
  unfold tk_at_R, tk_at. tk_lits.
  (* +0x1cc .. +0x1e0: &s->queued, its shadow byte address, s, &max_body and the two cfg shadow byte addresses back
     from the frame *)
  do 6 step.
  (* +0x1e4 bnez a0: the answer is not 0 *)
  step. tk_br true tk_cmp.
  tk_post. tk_ms.
Qed.

(* +0x21c .. +0x244 of an accepted turn: *has_display |= c->display, len += c->len and taken++ in the frame, to
   TK_J. *)
Local Ltac tk_okt hd disp MU WM ST CH FR :=
  (* +0x21c ld a4,0x18(sp); +0x220 lw a2,0(a4): *has_display *)
  step; step; rewrite TTake.tk_sx32_small by lia;
  (* +0x224 ld a3,0x88(sp); +0x228 add a3,a3,a1; +0x22c sd a3,0x88(sp) *)
  step; step; step;
  (* +0x230 ld a1,0x90(sp); +0x234 addiw a1,a1,1; +0x238 sd a1,0x90(sp) *)
  step; step; rewrite tk_addiw by lia; step;
  (* +0x23c or a0,a2,a0 *)
  step; rewrite ?(unsigned_lit hd), ?(unsigned_lit disp) by lia;
  (* +0x240 sw a0,0(a4); +0x244 j +0x2ac *)
  step; step;
  tk_post; split; [tk_ms|]; split; [exact MU|]; split; [exact WM|]; split; [exact ST|]; split; [exact CH | exact FR].

(* diginet_body_check accepted: the turn takes the command (:368-371) and stores *has_display. *)
Lemma tk_run_bc_ok : forall (RNG : ExecF.footprint)
    (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (gp tp : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (sp' lo i taken kept len clen disp hd bp blp hdp allow khd : Z) (j00 : word)
    (sv : list word),
  rw_cells rsegs m sp' (tk_fr (tk_spill bp blp hdp allow len taken j00 ++ sv)) -> length sv = 13%nat ->
  ExecF.rng RNG sp' TK_FRAME -> stk rsegs m lo sp' -> 0 <= sp' -> sp' + TK_FRAME < 2 ^ 63 ->
  ov_read_bytes rsegs m (wa (tk_sh (TK_Q0 + 32 * i + 24))) 1 = Some [Z_to_bv 8 0] ->
  ov_read_bytes rsegs m (wa (tk_sh (TK_Q0 + 32 * i + 25))) 1 = Some [Z_to_bv 8 0] ->
  ov_read_bytes rsegs m (wa (TK_Q0 + 32 * i + 24)) 1 = Some (TW.put 1 clen) ->
  ov_read_bytes rsegs m (wa (TK_Q0 + 32 * i + 25)) 1 = Some (TW.put 1 disp) ->
  ov_read_bytes rsegs m (wa (tk_sh hdp)) 1 = Some [Z_to_bv 8 khd] ->
  ExecF.rng RNG (tk_sh (TK_Q0 + 32 * i + 24)) 1 -> ExecF.rng RNG (tk_sh (TK_Q0 + 32 * i + 25)) 1 ->
  ExecF.rng RNG (TK_Q0 + 32 * i + 24) 1 -> ExecF.rng RNG (TK_Q0 + 32 * i + 25) 1 ->
  ExecF.rng RNG (tk_sh hdp) 1 -> ExecF.rng RNG hdp 4 ->
  rw_cells rsegs m hdp [C4 (Z_to_bv 64 hd)] ->
  (hdp + 4 <= sp' \/ sp' + TK_FRAME <= hdp) ->
  hdp mod 4 = 0 -> (khd = 0 \/ (hdp mod 8 + 3 < khd /\ khd < 8)) ->
  0 < hdp -> hdp + 4 < 2 ^ 63 ->
  0 <= i < 512 -> 0 <= taken < 512 -> 0 <= kept <= 512 -> 0 <= len <= 1484 -> 0 <= clen < 256 ->
  0 <= disp < 256 -> 0 <= hd < 256 ->
  ExecF.evtF rsegs RNG
    (fun ms' => exists (m1 : word -> option byte) (z9 z0 z1 z2 z3 z4 z26 : word),
       ms' = tk_at TK_J ra t1 t2 z9 z0 z1 z2 z3 z4 z26 t3 t4 t5 t6 gp tp F fc m1 sp' i kept /\
       munch [(sp', sp' + TK_FRAME); (hdp, hdp + 4)] m m1 /\ wmono rsegs m m1 /\ stk rsegs m1 lo sp' /\
       rw_cells rsegs m1 hdp [C4 (Z_to_bv 64 (Z.lor hd disp))] /\
       rw_cells rsegs m1 sp' (tk_fr (tk_spill bp blp hdp allow (len + clen) (taken + 1) j00 ++ sv)))
    (tk_at_R TK_R2 ra t0 t1 t2 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 gp tp F fc m sp' i kept len bp).
Proof.
  intros RNG ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 gp tp F fc m sp' lo i taken kept len clen disp hd bp blp
    hdp allow khd j00 sv FR LSV RFR ST HS0 HS1 RS4 RS5 RC RD RK GS4 GS5 GC GD GK GH CH DH HM HK Hh0 Hh1
    Hi Ht Hk Hl Hc Hd Hhd.
  destruct (tk_len13 sv LSV) as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & ->).
  cbn [tk_fr tk_spill map app] in FR |- *.
  unfold tk_at_R, tk_at. tk_lits.
  pose proof (munch_refl [(sp', sp' + 256); (hdp, hdp + 4)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (* +0x1cc .. +0x1e0: the spills back *)
  do 6 step.
  (* +0x1e4 bnez a0: the answer is 0 *)
  step. tk_br false ltac:(vm_compute; reflexivity).
  (* +0x1e8 lb a0,0(s1): the shadow byte of c->len; +0x1ec bnez a0 *)
  step. step. tk_br false ltac:(vm_compute; reflexivity).
  (* +0x1f0 addi a0,s4,0x6f9; +0x1f4 srli; +0x1f8 ld a2,0x70(sp); +0x1fc add; +0x200 lb a2,0(a1): the shadow
     byte of c->display *)
  step. replace (6157888 + 32 * i + 1785) with (6159648 + 32 * i + 25) by lia.
  step. rewrite tk_shr3 by lia. step. step. step.
  (* +0x204 lbu a1,0x6f8(s4): c->len; +0x208 bnez a2 *)
  step. rewrite tk_lbu_put by lia. step. tk_br false ltac:(vm_compute; reflexivity).
  (* +0x20c ld a0,0x20(sp): the shadow byte address of has_display; +0x210 lb a2,0(a0);
     +0x214 lbu a0,0x6f9(s4): c->display *)
  step. step. step. rewrite tk_lbu_put by lia.
  (* +0x218 bnez a2: the shadow check of has_display (slow path +0x370 .. +0x37c: ld, andi, addi, blt) *)
  step.
  destruct HK as [K0|[K1 K2]].
  - subst khd. tk_br false ltac:(vm_compute; reflexivity).
    tk_okt hd disp MU WM ST CH FR.
  - tk_br true ltac:(rewrite sxb_eq0, tk_signed8 by lia; tk_zc).
    step. step. step. step.
    tk_br true ltac:(rewrite (unsigned_lit hdp), land7 by lia; rewrite lts_low by lia;
                     rewrite tk_signed8 by lia; tk_zc).
    tk_okt hd disp MU WM ST CH FR.
Qed.

(* ---- the refusal (:373-375) ---- *)

(* kept = i: no copy, kept++ only. *)
Lemma tk_run_nf_eq : forall (RNG : ExecF.footprint)
    (ra t1 t2 s1 a0 a1 a2 a3 a4 s10 t3 t4 t5 t6 : word) (gp tp : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (sp' i kept : Z),
  0 <= i < 512 -> kept = i ->
  ExecF.evtF rsegs RNG
    (fun ms' => exists (z0 : word),
       ms' = tk_at TK_J ra t1 t2 s1 z0 a1 a2 a3 a4 s10 t3 t4 t5 t6 gp tp F fc m sp' i (kept + 1))
    (tk_at TK_NF ra t1 t2 s1 a0 a1 a2 a3 a4 s10 t3 t4 t5 t6 gp tp F fc m sp' i kept).
Proof.
  intros RNG ra t1 t2 s1 a0 a1 a2 a3 a4 s10 t3 t4 t5 t6 gp tp F fc m sp' i kept Hi E.
  subst kept. unfold tk_at. tk_lits.
  (* +0x268 slli a0,s5,32; +0x26c srli a0,a0,32: a0 = kept *)
  step. step. rewrite (TTake.tk_zext32 i) by lia.
  (* +0x270 beq s11,a0: kept = i *)
  step. tk_br true ltac:(apply bv_eqb_refl).
  (* +0x2a8 addiw s5,s5,1 *)
  step. rewrite tk_addiw by lia.
  tk_post. tk_ms.
Qed.

(* kept <> i: the copy of :374, after its two UBSan checks (512 < kept, &s->queue[0] + 32 kept wrapping). *)
Lemma tk_run_nf_cpy : forall (RNG : ExecF.footprint)
    (ra t1 t2 s1 a0 a1 a2 a3 a4 s10 t3 t4 t5 t6 : word) (gp tp : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (sp' i taken kept len bp blp hdp allow : Z) (j00 : word) (sv : list word),
  rw_cells rsegs m sp' (tk_fr (tk_spill bp blp hdp allow len taken j00 ++ sv)) -> length sv = 13%nat ->
  ExecF.rng RNG sp' TK_FRAME -> 0 <= sp' -> sp' + TK_FRAME < 2 ^ 63 ->
  0 <= i < 512 -> 0 <= kept < 512 -> kept <> i ->
  ExecF.evtF rsegs RNG
    (fun ms' =>
       ms' = MS (mkR (Z_to_bv 64 TK_R3) (Z_to_bv 64 sp') gp tp (Z_to_bv 64 (tk_sh TK_MAXB)) t1 t2
                     (Z_to_bv 64 TK_NQ0) s1 (Z_to_bv 64 (TK_Q0 + 32 * kept)) (Z_to_bv 64 (TK_Q0 + 32 * i))
                     (Z_to_bv 64 32) a3 a4 (Z_to_bv 64 TK_QD) (Z_to_bv 64 TK_MAXB) (Z_to_bv 64 (tk_sh TK_MAXC))
                     (Z_to_bv 64 TK_S) (Z_to_bv 64 (32 * i)) (Z_to_bv 64 (TK_S + 32 * i)) (Z_to_bv 64 kept)
                     (Z_to_bv 64 (- i)) (Z_to_bv 64 TK_MAXC) (Z_to_bv 64 (tk_sh TK_QD))
                     (Z_to_bv 64 (TK_Q0 + 32 * i)) s10 (Z_to_bv 64 i) t3 t4 t5 t6)
                F (Z_to_bv 64 TK_MEMCPY) fc None m (seg_rom rsegs))
    (tk_at TK_NF ra t1 t2 s1 a0 a1 a2 a3 a4 s10 t3 t4 t5 t6 gp tp F fc m sp' i kept).
Proof.
  intros RNG ra t1 t2 s1 a0 a1 a2 a3 a4 s10 t3 t4 t5 t6 gp tp F fc m sp' i taken kept len bp blp hdp allow j00 sv
    FR LSV RFR HS0 HS1 Hi Hk HK.
  cbn [tk_fr tk_spill map app] in FR.
  unfold tk_at. tk_lits.
  (* +0x268 .. +0x26c: a0 = kept; +0x270 beq s11,a0: kept <> i *)
  step. step. rewrite (TTake.tk_zext32 kept) by lia.
  step. tk_br false tk_cmp.
  (* +0x274 li a1,512; +0x278 bltu a1,s5 (to the trap): kept <= 512 *)
  step. step. tk_br false tk_cmp.
  (* +0x27c slli a0,a0,5; +0x280 bltu s0,a0 (to the trap): &s->queue[0] + 32 kept does not wrap *)
  step. rewrite tk_shl5 by lia. step. tk_br false tk_cmp.
  (* +0x284 ld a1,0x78(sp): &s->queue[0]; +0x288 add a0,a1,a0; +0x28c li a2,32; +0x290 mv a1,s9; +0x294 the call *)
  step. step. step. step. step.
  tk_post. tk_ms.
Qed.

(* The return of the copy of :374: the spills come back, kept++. *)
Lemma tk_run_nf_ret : forall (RNG : ExecF.footprint)
    (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 t5 t6 : word) (gp tp : word) (F : bvmap 5 word)
    (fc : bv 32) (m : word -> option byte) (sp' i taken kept len bp blp hdp allow : Z) (j00 : word)
    (sv : list word),
  rw_cells rsegs m sp' (tk_fr (tk_spill bp blp hdp allow len taken j00 ++ sv)) -> length sv = 13%nat ->
  ExecF.rng RNG sp' TK_FRAME -> 0 <= sp' -> sp' + TK_FRAME < 2 ^ 63 ->
  0 <= i < 512 -> 0 <= kept < 512 ->
  ExecF.evtF rsegs RNG
    (fun ms' => ms' = tk_at TK_J ra t1 t2 s1 a0 a1 a2 a3 a4 s10 t3 t4 t5 t6 gp tp F fc m sp' i (kept + 1))
    (MS (mkR ra (Z_to_bv 64 sp') gp tp t0 t1 t2 (Z_to_bv 64 TK_NQ0) s1 a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 TK_S) (Z_to_bv 64 (32 * i)) (Z_to_bv 64 (TK_S + 32 * i)) (Z_to_bv 64 kept)
             (Z_to_bv 64 (- i)) (Z_to_bv 64 TK_MAXC) (Z_to_bv 64 (tk_sh TK_QD)) (Z_to_bv 64 (TK_Q0 + 32 * i))
             s10 (Z_to_bv 64 i) t3 t4 t5 t6)
        F (Z_to_bv 64 TK_R3) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 t5 t6 gp tp F fc m sp' i taken kept len bp blp hdp
    allow j00 sv FR LSV RFR HS0 HS1 Hi Hk.
  cbn [tk_fr tk_spill map app] in FR.
  unfold tk_at. tk_lits.
  (* +0x298 .. +0x2a4: t0, a7, a6, a5 back from the frame; +0x2a8 addiw s5,s5,1 *)
  do 4 step. step. rewrite tk_addiw by lia.
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

(* +0x2ac .. +0x2d0: the shadow check of max_cmds, max_cmds against taken (frame), the shadow check of max_body,
   max_body against len (frame); the branch of the second test left open. *)
Local Ltac tk_j1 :=
  step; step; tk_br false ltac:(vm_compute; reflexivity);
  step; rewrite tk_lw_put; step; step; tk_br false tk_cmp;
  step; step; tk_br false ltac:(vm_compute; reflexivity);
  step; rewrite tk_lwu_put by lia; step; step.

(* +0x2d4 .. +0x2ec: the shadow check of s->queued, s->queued, i + 1 / 32 (i + 1) / -(i + 1); the branch of
   i + 1 < s->queued left open. *)
Local Ltac tk_j2 :=
  step; step; tk_br false ltac:(vm_compute; reflexivity);
  step; rewrite tk_lwu_put by lia; step; step; step; step.

(* Neither counter is full and a turn is left: back to the loop head with i + 1. *)
Lemma tk_run_join_next : forall (RNG : ExecF.footprint)
    (ra t1 t2 s1 a0 a1 a2 a3 a4 s10 t3 t4 t5 t6 : word) (gp tp : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (sp' i taken kept len maxc maxb queued bp blp hdp allow : Z) (j00 : word)
    (sv : list word),
  tk_rd_join m maxc maxb queued -> tk_rng_join RNG ->
  rw_cells rsegs m sp' (tk_fr (tk_spill bp blp hdp allow len taken j00 ++ sv)) -> length sv = 13%nat ->
  ExecF.rng RNG sp' TK_FRAME -> 0 <= sp' -> sp' + TK_FRAME < 2 ^ 63 ->
  0 <= i < 512 -> 0 <= taken <= 512 -> 0 <= kept <= 512 -> 0 <= len <= 1484 ->
  0 <= maxc < 2 ^ 32 -> 0 <= maxb < 2 ^ 32 -> 0 <= queued <= 512 ->
  taken <> maxc -> len <> maxb -> i + 1 < queued ->
  ExecF.evtF rsegs RNG
    (fun ms' => exists (z0 z1 z4 z9 : word),
       ms' = tk_at_L ra t1 t2 s1 z0 z1 a2 a3 a4 z4 z9 s10 t3 t4 t5 t6 gp tp F fc m sp' (i + 1) kept)
    (tk_at TK_J ra t1 t2 s1 a0 a1 a2 a3 a4 s10 t3 t4 t5 t6 gp tp F fc m sp' i kept).
Proof.
  intros RNG ra t1 t2 s1 a0 a1 a2 a3 a4 s10 t3 t4 t5 t6 gp tp F fc m sp' i taken kept len maxc maxb queued
    bp blp hdp allow j00 sv RD RG FR LSV RFR HS0 HS1 Hi Ht Hk Hl HC HB HQ HTC HLB HN.
  destruct RD as (J1 & J2 & J3 & J4 & J5 & J6). destruct RG as (K1 & K2 & K3 & K4 & K5 & K6).
  cbn [tk_fr tk_spill map app] in FR.
  unfold tk_at, tk_at_L. tk_lits.
  tk_j1.
  (* +0x2d0 beq a1,a0: len <> max_body *)
  tk_br false tk_cmp.
  tk_j2.
  (* +0x2ec bltu s11,a0: i + 1 < s->queued *)
  tk_br true tk_cmp.
  tk_post. tk_ms.
Qed.

(* Neither counter is full and no turn is left: the exit. *)
Lemma tk_run_join_exit : forall (RNG : ExecF.footprint)
    (ra t1 t2 s1 a0 a1 a2 a3 a4 s10 t3 t4 t5 t6 : word) (gp tp : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (sp' i taken kept len maxc maxb queued bp blp hdp allow : Z) (j00 : word)
    (sv : list word),
  tk_rd_join m maxc maxb queued -> tk_rng_join RNG ->
  rw_cells rsegs m sp' (tk_fr (tk_spill bp blp hdp allow len taken j00 ++ sv)) -> length sv = 13%nat ->
  ExecF.rng RNG sp' TK_FRAME -> 0 <= sp' -> sp' + TK_FRAME < 2 ^ 63 ->
  0 <= i < 512 -> 0 <= taken <= 512 -> 0 <= kept <= 512 -> 0 <= len <= 1484 ->
  0 <= maxc < 2 ^ 32 -> 0 <= maxb < 2 ^ 32 -> 0 <= queued <= 512 ->
  taken <> maxc -> len <> maxb -> queued <= i + 1 ->
  ExecF.evtF rsegs RNG
    (fun ms' => exists (z0 z1 z19 z22 z27 : word),
       ms' = MS (mkR ra (Z_to_bv 64 sp') gp tp (Z_to_bv 64 (tk_sh TK_MAXB)) t1 t2 (Z_to_bv 64 TK_NQ0) s1 z0 z1
                     a2 a3 a4 (Z_to_bv 64 TK_QD) (Z_to_bv 64 TK_MAXB) (Z_to_bv 64 (tk_sh TK_MAXC))
                     (Z_to_bv 64 TK_S) z19 (Z_to_bv 64 (TK_S + 32 * i)) (Z_to_bv 64 kept) z22
                     (Z_to_bv 64 TK_MAXC) (Z_to_bv 64 (tk_sh TK_QD)) (Z_to_bv 64 (TK_Q0 + 32 * i)) s10 z27
                     t3 t4 t5 t6)
                F (Z_to_bv 64 TK_X) fc None m (seg_rom rsegs))
    (tk_at TK_J ra t1 t2 s1 a0 a1 a2 a3 a4 s10 t3 t4 t5 t6 gp tp F fc m sp' i kept).
Proof.
  intros RNG ra t1 t2 s1 a0 a1 a2 a3 a4 s10 t3 t4 t5 t6 gp tp F fc m sp' i taken kept len maxc maxb queued
    bp blp hdp allow j00 sv RD RG FR LSV RFR HS0 HS1 Hi Ht Hk Hl HC HB HQ HTC HLB HN.
  destruct RD as (J1 & J2 & J3 & J4 & J5 & J6). destruct RG as (K1 & K2 & K3 & K4 & K5 & K6).
  cbn [tk_fr tk_spill map app] in FR.
  unfold tk_at. tk_lits.
  tk_j1.
  tk_br false tk_cmp.
  tk_j2.
  (* +0x2ec bltu s11,a0: s->queued <= i + 1; +0x2f0 j +0x44c *)
  tk_br false tk_cmp. step.
  tk_post. tk_ms.
Qed.

(* A counter is full: the break of :377, to the tail. *)
Lemma tk_run_join_break : forall (RNG : ExecF.footprint)
    (ra t1 t2 s1 a0 a1 a2 a3 a4 s10 t3 t4 t5 t6 : word) (gp tp : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (sp' i taken kept len maxc maxb queued bp blp hdp allow : Z) (j00 : word)
    (sv : list word),
  tk_rd_join m maxc maxb queued -> tk_rng_join RNG ->
  rw_cells rsegs m sp' (tk_fr (tk_spill bp blp hdp allow len taken j00 ++ sv)) -> length sv = 13%nat ->
  ExecF.rng RNG sp' TK_FRAME -> 0 <= sp' -> sp' + TK_FRAME < 2 ^ 63 ->
  0 <= i < 512 -> 0 <= taken <= 512 -> 0 <= kept <= 512 -> 0 <= len <= 1484 ->
  0 <= maxc < 2 ^ 32 -> 0 <= maxb < 2 ^ 32 -> 0 <= queued <= 512 ->
  (taken = maxc \/ len = maxb) ->
  ExecF.evtF rsegs RNG
    (fun ms' => exists (z0 z1 : word),
       ms' = tk_at TK_BRK ra t1 t2 s1 z0 z1 a2 a3 a4 s10 t3 t4 t5 t6 gp tp F fc m sp' i kept)
    (tk_at TK_J ra t1 t2 s1 a0 a1 a2 a3 a4 s10 t3 t4 t5 t6 gp tp F fc m sp' i kept).
Proof.
  intros RNG ra t1 t2 s1 a0 a1 a2 a3 a4 s10 t3 t4 t5 t6 gp tp F fc m sp' i taken kept len maxc maxb queued
    bp blp hdp allow j00 sv RD RG FR LSV RFR HS0 HS1 Hi Ht Hk Hl HC HB HQ HF.
  destruct RD as (J1 & J2 & J3 & J4 & J5 & J6). destruct RG as (K1 & K2 & K3 & K4 & K5 & K6).
  cbn [tk_fr tk_spill map app] in FR.
  unfold tk_at. tk_lits.
  (* +0x2ac .. +0x2b8: the shadow check of max_cmds, max_cmds, taken back *)
  step. step. tk_br false ltac:(vm_compute; reflexivity).
  step. rewrite tk_lw_put. step. step.
  destruct (Z.eq_dec taken maxc) as [E|E].
  - (* +0x2bc beq a1,a0: taken = max_cmds *)
    tk_br true tk_cmp.
    tk_post. tk_ms.
  - (* taken <> max_cmds, so len = max_body: +0x2c0 .. +0x2d0 *)
    assert (EB : len = maxb) by (destruct HF; [contradiction | exact H]).
    tk_br false tk_cmp.
    step. step. tk_br false ltac:(vm_compute; reflexivity).
    step. rewrite tk_lwu_put by lia. step. step. tk_br true tk_cmp.
    tk_post. tk_ms.
Qed.

(* ---- the tail (:378-380) ---- *)

(* The state at the tail loop head, turn j: s1 = j - 1, s2 = 32 j, s3 = &s->queue[j], s4 = 511, s5 = kept,
   s6 = j - kept + 513 (the j at which kept would reach 513: constant through the tail, as both count up), s7 = 3,
   s11 = j. ra, t0 .. t2, a0 .. a4, a6, a7, s9, s10 are free: the loop never reads them, and each copy clobbers the
   caller-saved ones. *)
Definition tk_at_TL (ra t0 t1 t2 a0 a1 a2 a3 a4 a6 a7 s9 s10 t3 t4 t5 t6 : word) (gp tp : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (sp' j kept : Z) : machine_state :=
  MS (mkR ra (Z_to_bv 64 sp') gp tp t0 t1 t2 (Z_to_bv 64 TK_NQ0) (Z_to_bv 64 (j - 1)) a0 a1 a2 a3 a4
          (Z_to_bv 64 TK_QD) a6 a7 (Z_to_bv 64 (32 * j)) (Z_to_bv 64 (TK_Q0 + 32 * j)) (Z_to_bv 64 511)
          (Z_to_bv 64 kept) (Z_to_bv 64 (j - kept + 513)) (Z_to_bv 64 3) (Z_to_bv 64 (tk_sh TK_QD)) s9 s10
          (Z_to_bv 64 j) t3 t4 t5 t6)
     F (Z_to_bv 64 TK_TL) fc None m (seg_rom rsegs).

(* +0x388 .. +0x39c: the shadow check of s->queued, s->queued, a1 = 1 - (-i) = i + 1 (subw of s6); the branch of
   i + 1 >= s->queued left open. *)
Local Ltac tk_b1 i :=
  step; step; tk_br false ltac:(vm_compute; reflexivity);
  step; rewrite tk_lw_put, tk_s32_small by lia;
  step; step;
  rewrite ?(unsigned_lit 1) by lia; rewrite tk_swrap_sub_neg; rewrite (TTake.tk_swrap32_small (1 + i)) by lia;
  step.

(* The break's own code: a turn is left, so the tail loop runs from j = i + 1. *)
Lemma tk_run_break_tail : forall (RNG : ExecF.footprint)
    (ra t1 t2 s1 a0 a1 a2 a3 a4 s10 t3 t4 t5 t6 : word) (gp tp : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (sp' i kept queued : Z),
  ov_read_bytes rsegs m (wa (tk_sh TK_QD)) 1 = Some [Z_to_bv 8 0] ->
  ov_read_bytes rsegs m (wa TK_QD) 4 = Some (TW.put 4 queued) ->
  ExecF.rng RNG (tk_sh TK_QD) 1 -> ExecF.rng RNG TK_QD 4 ->
  0 <= i < 512 -> 0 <= kept <= i + 1 -> 0 <= queued <= 512 ->
  i + 1 < queued ->
  ExecF.evtF rsegs RNG
    (fun ms' => exists (z0 z1 : word),
       ms' = tk_at_TL ra (Z_to_bv 64 (tk_sh TK_MAXB)) t1 t2 z0 z1 a2 a3 a4 (Z_to_bv 64 TK_MAXB)
               (Z_to_bv 64 (tk_sh TK_MAXC)) (Z_to_bv 64 (TK_Q0 + 32 * i)) s10 t3 t4 t5 t6 gp tp F fc m
               sp' (i + 1) kept)
    (tk_at TK_BRK ra t1 t2 s1 a0 a1 a2 a3 a4 s10 t3 t4 t5 t6 gp tp F fc m sp' i kept).
Proof.
  intros RNG ra t1 t2 s1 a0 a1 a2 a3 a4 s10 t3 t4 t5 t6 gp tp F fc m sp' i kept queued RS RQ GS GQ Hi Hk HQ HN.
  unfold tk_at, tk_at_TL. tk_lits.
  tk_b1 i.
  (* +0x39c bgeu a1,a0: i + 1 < s->queued *)
  tk_br false tk_cmp.
  (* +0x3a0 negw s1,s6: s1 = i *)
  step.
  rewrite ?(unsigned_lit 0) by lia. rewrite tk_swrap_sub_neg. rewrite (TTake.tk_swrap32_small (0 + i)) by lia.
  (* +0x3a4 addi s2,s3,32; +0x3a8 addi s3,s4,0x700; +0x3ac addi s11,s11,1; +0x3b0 li a0,513 *)
  do 4 step.
  (* +0x3b4 subw a0,a0,s5: 513 - kept *)
  step.
  rewrite ?(unsigned_lit 513) by lia. rewrite (unsigned_lit kept) by lia.
  rewrite (TTake.tk_swrap32_small (513 - kept)) by lia.
  (* +0x3b8 sltiu a1,a0,514 *)
  step. rewrite (tk_sltiu1 (513 - kept)) by lia.
  (* +0x3bc negw a1,a1 *)
  step.
  rewrite ?(unsigned_lit 0) by lia. rewrite ?(unsigned_lit 1) by lia. try change (bv_swrap 32 (0 - 1)) with (-1).
  (* +0x3c0 and a0,a1,a0 *)
  step. rewrite (tk_land_m1 (513 - kept)) by lia.
  (* +0x3c4 li s4,511; +0x3c8 subw a0,a0,s6: 513 - kept + i *)
  step. step.
  rewrite (unsigned_lit (513 - kept)) by lia. rewrite tk_swrap_sub_neg.
  rewrite (TTake.tk_swrap32_small (513 - kept + i)) by lia.
  (* +0x3cc andi s7,a5,7; +0x3d0 addi a0,a0,1; +0x3d4 slli a0,a0,32; +0x3d8 srli s6,a0,32 *)
  step. step. step. step. rewrite (TTake.tk_zext32 (513 - kept + i + 1)) by lia.
  (* +0x3dc addi s7,s7,3 *)
  step.
  tk_post. tk_ms.
Qed.

(* The break with no turn left: straight to the exit. *)
Lemma tk_run_break_exit : forall (RNG : ExecF.footprint)
    (ra t1 t2 s1 a0 a1 a2 a3 a4 s10 t3 t4 t5 t6 : word) (gp tp : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (sp' i kept queued : Z),
  ov_read_bytes rsegs m (wa (tk_sh TK_QD)) 1 = Some [Z_to_bv 8 0] ->
  ov_read_bytes rsegs m (wa TK_QD) 4 = Some (TW.put 4 queued) ->
  ExecF.rng RNG (tk_sh TK_QD) 1 -> ExecF.rng RNG TK_QD 4 ->
  0 <= i < 512 -> 0 <= kept <= 512 -> 0 <= queued <= 512 ->
  queued <= i + 1 ->
  ExecF.evtF rsegs RNG
    (fun ms' => exists (z0 z1 : word),
       ms' = tk_at TK_X ra t1 t2 s1 z0 z1 a2 a3 a4 s10 t3 t4 t5 t6 gp tp F fc m sp' i kept)
    (tk_at TK_BRK ra t1 t2 s1 a0 a1 a2 a3 a4 s10 t3 t4 t5 t6 gp tp F fc m sp' i kept).
Proof.
  intros RNG ra t1 t2 s1 a0 a1 a2 a3 a4 s10 t3 t4 t5 t6 gp tp F fc m sp' i kept queued RS RQ GS GQ Hi Hk HQ HN.
  unfold tk_at. tk_lits.
  tk_b1 i.
  (* +0x39c bgeu a1,a0: s->queued <= i + 1 *)
  tk_br true tk_cmp.
  tk_post. tk_ms.
Qed.

(* The tail turn: the copy of :379, after its four UBSan checks (kept = 513, &s->queue[0] + 32 kept wrapping,
   511 < j - 1, &s->queue[0] + 32 j wrapping). *)
Lemma tk_run_tail_cpy : forall (RNG : ExecF.footprint)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a6 a7 s9 s10 t3 t4 t5 t6 : word) (gp tp : word) (F : bvmap 5 word)
    (fc : bv 32) (m : word -> option byte) (sp' j kept bp blp hdp allow len taken : Z) (j00 : word)
    (sv : list word),
  rw_cells rsegs m sp' (tk_fr (tk_spill bp blp hdp allow len taken j00 ++ sv)) -> length sv = 13%nat ->
  ExecF.rng RNG sp' TK_FRAME -> 0 <= sp' -> sp' + TK_FRAME < 2 ^ 63 ->
  1 <= j < 512 -> 0 <= kept < 512 ->
  ExecF.evtF rsegs RNG
    (fun ms' =>
       ms' = MS (mkR (Z_to_bv 64 TK_R4) (Z_to_bv 64 sp') gp tp t0 t1 t2 (Z_to_bv 64 TK_NQ0) (Z_to_bv 64 (j - 1))
                     (Z_to_bv 64 (TK_Q0 + 32 * kept)) (Z_to_bv 64 (TK_Q0 + 32 * j)) (Z_to_bv 64 32) a3 a4
                     (Z_to_bv 64 TK_QD) a6 a7 (Z_to_bv 64 (32 * j)) (Z_to_bv 64 (TK_Q0 + 32 * j)) (Z_to_bv 64 511)
                     (Z_to_bv 64 kept) (Z_to_bv 64 (j - kept + 513)) (Z_to_bv 64 3) (Z_to_bv 64 (tk_sh TK_QD))
                     s9 s10 (Z_to_bv 64 j) t3 t4 t5 t6)
                F (Z_to_bv 64 TK_MEMCPY) fc None m (seg_rom rsegs))
    (tk_at_TL ra t0 t1 t2 a0 a1 a2 a3 a4 a6 a7 s9 s10 t3 t4 t5 t6 gp tp F fc m sp' j kept).
Proof.
  intros RNG ra t0 t1 t2 a0 a1 a2 a3 a4 a6 a7 s9 s10 t3 t4 t5 t6 gp tp F fc m sp' j kept bp blp hdp allow len taken
    j00 sv FR LSV RFR HS0 HS1 Hj Hk.
  cbn [tk_fr tk_spill map app] in FR.
  unfold tk_at_TL. tk_lits.
  (* +0x3e0 beq s6,s11 (to the trap): kept <> 513 *)
  step. tk_br false tk_cmp.
  (* +0x3e4 slli a0,s5,5; +0x3e8 bltu s0,a0 (to the trap) *)
  step. rewrite tk_shl5 by lia. step. tk_br false tk_cmp.
  (* +0x3ec bltu s4,s1 (to the trap): j - 1 <= 511; +0x3f0 bltu s0,s2 (to the trap) *)
  step. tk_br false tk_cmp. step. tk_br false tk_cmp.
  (* +0x3f4 ld a1,0x78(sp): &s->queue[0]; +0x3f8 add a0,a1,a0; +0x3fc li a2,32; +0x400 mv a1,s3; +0x404 the call *)
  step. step. step. step. step.
  tk_post. tk_ms.
Qed.

(* +0x408 .. +0x42c: the shadow check of s->queued, j + 1, &s->queued back, s->queued, s1 / s3 / s2 / kept up;
   the branch of j + 1 < s->queued left open. *)
Local Ltac tk_t1 :=
  step; step; tk_br false ltac:(vm_compute; reflexivity);
  step; step; step; rewrite tk_lwu_put by lia;
  step; rewrite tk_addiw by lia; step; step; step; rewrite tk_addiw by lia;
  step.

(* The return of the tail copy, with a turn left. *)
Lemma tk_run_tail_next : forall (RNG : ExecF.footprint)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 s10 t3 t4 t5 t6 : word) (gp tp : word) (F : bvmap 5 word)
    (fc : bv 32) (m : word -> option byte) (sp' j kept queued bp blp hdp allow len taken : Z) (j00 : word)
    (sv : list word),
  rw_cells rsegs m sp' (tk_fr (tk_spill bp blp hdp allow len taken j00 ++ sv)) -> length sv = 13%nat ->
  ExecF.rng RNG sp' TK_FRAME -> 0 <= sp' -> sp' + TK_FRAME < 2 ^ 63 ->
  ov_read_bytes rsegs m (wa (tk_sh TK_QD)) 1 = Some [Z_to_bv 8 0] ->
  ov_read_bytes rsegs m (wa TK_QD) 4 = Some (TW.put 4 queued) ->
  ExecF.rng RNG (tk_sh TK_QD) 1 -> ExecF.rng RNG TK_QD 4 ->
  1 <= j < 512 -> 0 <= kept < 512 -> 0 <= queued <= 512 ->
  j + 1 < queued ->
  ExecF.evtF rsegs RNG
    (fun ms' => exists (z0 : word),
       ms' = tk_at_TL ra t0 t1 t2 z0 a1 a2 a3 a4 a6 a7 s9 s10 t3 t4 t5 t6 gp tp F fc m sp' (j + 1) (kept + 1))
    (MS (mkR ra (Z_to_bv 64 sp') gp tp t0 t1 t2 (Z_to_bv 64 TK_NQ0) (Z_to_bv 64 (j - 1)) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (32 * j)) (Z_to_bv 64 (TK_Q0 + 32 * j)) (Z_to_bv 64 511) (Z_to_bv 64 kept)
             (Z_to_bv 64 (j - kept + 513)) (Z_to_bv 64 3) (Z_to_bv 64 (tk_sh TK_QD)) s9 s10 (Z_to_bv 64 j)
             t3 t4 t5 t6)
        F (Z_to_bv 64 TK_R4) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 s10 t3 t4 t5 t6 gp tp F fc m sp' j kept queued bp blp hdp allow
    len taken j00 sv FR LSV RFR HS0 HS1 RS RQ GS GQ Hj Hk HQ HN.
  cbn [tk_fr tk_spill map app] in FR.
  unfold tk_at_TL. tk_lits.
  tk_t1.
  (* +0x42c bltu s11,a0: j + 1 < s->queued *)
  tk_br true tk_cmp.
  tk_post. tk_ms.
Qed.

(* The return of the tail copy, with no turn left: the exit. *)
Lemma tk_run_tail_done : forall (RNG : ExecF.footprint)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 s10 t3 t4 t5 t6 : word) (gp tp : word) (F : bvmap 5 word)
    (fc : bv 32) (m : word -> option byte) (sp' j kept queued bp blp hdp allow len taken : Z) (j00 : word)
    (sv : list word),
  rw_cells rsegs m sp' (tk_fr (tk_spill bp blp hdp allow len taken j00 ++ sv)) -> length sv = 13%nat ->
  ExecF.rng RNG sp' TK_FRAME -> 0 <= sp' -> sp' + TK_FRAME < 2 ^ 63 ->
  ov_read_bytes rsegs m (wa (tk_sh TK_QD)) 1 = Some [Z_to_bv 8 0] ->
  ov_read_bytes rsegs m (wa TK_QD) 4 = Some (TW.put 4 queued) ->
  ExecF.rng RNG (tk_sh TK_QD) 1 -> ExecF.rng RNG TK_QD 4 ->
  1 <= j < 512 -> 0 <= kept < 512 -> 0 <= queued <= 512 ->
  queued <= j + 1 ->
  ExecF.evtF rsegs RNG
    (fun ms' => exists (z0 : word),
       ms' = MS (mkR ra (Z_to_bv 64 sp') gp tp t0 t1 t2 (Z_to_bv 64 TK_NQ0) (Z_to_bv 64 j) z0 a1 a2 a3 a4
                     (Z_to_bv 64 TK_QD) a6 a7 (Z_to_bv 64 (32 * (j + 1))) (Z_to_bv 64 (TK_Q0 + 32 * (j + 1)))
                     (Z_to_bv 64 511) (Z_to_bv 64 (kept + 1)) (Z_to_bv 64 (j - kept + 513)) (Z_to_bv 64 3)
                     (Z_to_bv 64 (tk_sh TK_QD)) s9 s10 (Z_to_bv 64 (j + 1)) t3 t4 t5 t6)
                F (Z_to_bv 64 TK_X) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 sp') gp tp t0 t1 t2 (Z_to_bv 64 TK_NQ0) (Z_to_bv 64 (j - 1)) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (32 * j)) (Z_to_bv 64 (TK_Q0 + 32 * j)) (Z_to_bv 64 511) (Z_to_bv 64 kept)
             (Z_to_bv 64 (j - kept + 513)) (Z_to_bv 64 3) (Z_to_bv 64 (tk_sh TK_QD)) s9 s10 (Z_to_bv 64 j)
             t3 t4 t5 t6)
        F (Z_to_bv 64 TK_R4) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 s10 t3 t4 t5 t6 gp tp F fc m sp' j kept queued bp blp hdp allow
    len taken j00 sv FR LSV RFR HS0 HS1 RS RQ GS GQ Hj Hk HQ HN.
  cbn [tk_fr tk_spill map app] in FR.
  tk_lits.
  tk_t1.
  (* +0x42c bltu s11,a0: s->queued <= j + 1; +0x430 j +0x44c *)
  tk_br false tk_cmp. step.
  tk_post. tk_ms.
Qed.

(* ---- the exit (:383-385) ---- *)

(* s->queued = kept, *body_len = len (from the frame), a0 = taken (from the frame), the epilogue. The 4-byte store
   at s->queued and the 8-byte store at body_len are the last two writes; the saved registers come back from the
   frame. *)
Lemma tk_run_exit : forall (RNG : ExecF.footprint)
    (ra0 t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a6 a7 s2 s3 s4 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) (gp tp : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (sp' lo taken kept len blp kbl queued0 : Z) (ws : list word)
    (v11 v10 v9 v8 v7 v6 v5 v4 v3 v2 v1 v0 vra : word),
  rw_cells rsegs m sp' (tk_fr (ws ++ tk_saved v11 v10 v9 v8 v7 v6 v5 v4 v3 v2 v1 v0 vra)) ->
  tk_xfr ws blp len taken ->
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
    (fun ms' => exists (m1 : word -> option byte) (spx x11 x12 : word),
       ms' = MS (mkR vra spx gp tp t0 t1 t2 v0 v1 (Z_to_bv 64 taken) x11 x12 a3 a4 (Z_to_bv 64 TK_QD) a6 a7
                     v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 t3 t4 t5 t6)
                F (ret_pc vra) fc None m1 (seg_rom rsegs) /\
       bv_unsigned spx = sp' + TK_FRAME /\
       munch [(TK_QD, TK_QD + 4); (blp, blp + 8)] m m1 /\ wmono rsegs m m1 /\
       stk rsegs m1 lo (sp' + TK_FRAME) /\
       rw_cells rsegs m1 TK_QD [C4 (Z_to_bv 64 kept)] /\
       rw_cells rsegs m1 blp [C8 (Z_to_bv 64 len)])
    (MS (mkR ra0 (Z_to_bv 64 sp') gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 (Z_to_bv 64 TK_QD) a6 a7 s2 s3 s4
             (Z_to_bv 64 kept) s6 s7 (Z_to_bv 64 (tk_sh TK_QD)) s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 TK_X) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a6 a7 s2 s3 s4 s6 s7 s9 s10 s11 t3 t4 t5 t6 gp tp F fc m sp' lo taken
    kept len blp kbl queued0 ws v11 v10 v9 v8 v7 v6 v5 v4 v3 v2 v1 v0 vra FR XF RFR ST HS0 HS1 RSQ RSB GSQ GSB
    GQ GB CQ CB D1 D2 D3 D4 HKB HBM HB0 HB1 Ht Hk Hl.
  destruct XF as (LWS & N7 & N14 & N17 & N18).
  destruct (tk_len19 ws LWS) as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 &
    w15 & w16 & w17 & w18 & ->).
  cbn [nth] in N7, N14, N17, N18. subst w7 w14 w17 w18 kbl. destruct CB as [junk CB].
  cbn [tk_fr tk_saved map app] in FR.
  tk_lits.
  pose proof (munch_refl [(6176032, 6176032 + 4); (blp, blp + 8)] m) as MU.
  pose proof (munch_refl [(6176032, 6176032 + 4)] m) as MQ.
  pose proof (wmono_refl rsegs m) as WM.
  (* +0x44c lb a0,0(s8): the shadow byte of s->queued; +0x450 bnez a0. The cell of s->queued is kept out of
     sight of the load: StepF's load reads an rw_cells fact at the literal distance of two literal addresses,
     which here is 2^31 cells. *)
  pose proof (tk_hid_intro _ CQ) as CQh. clear CQ.
  step. step. tk_br false ltac:(vm_compute; reflexivity).
  unfold tk_hid in CQh. rename CQh into CQ.
  (* +0x454 ld a0,0x38(sp): body_len; +0x458 andi a1,a0,7 *)
  step. step. rewrite (tk_land7 blp) by lia.
  (* +0x45c sw s5,0(a5): s->queued = kept; +0x460 bnez a1 (to the trap) *)
  step. step. tk_br false ltac:(vm_compute; reflexivity).
  (* +0x464 srli a1,a0,3; +0x468 ld a2,0x70(sp): the shadow base; +0x46c add a1,a1,a2;
     +0x470 lbu a1,0(a1): the shadow byte of body_len *)
  step. rewrite tk_shr3 by lia. step. step.
  tk_rd MQ RSB. clear MQ. step.
  (* +0x474 bnez a1 *)
  step. tk_br false ltac:(vm_compute; reflexivity).
  (* +0x478 ld a1,0x88(sp): len; +0x47c sd a1,0(a0): *body_len = len; +0x480 ld a0,0x90(sp): taken *)
  step. step. step.
  (* +0x484 .. +0x4b4: the saved registers back; +0x4b8 addi sp,sp,0x100; +0x4bc ret *)
  do 15 step.
  pose proof (tk_release _ _ _ _ ST FR) as ST'. cbn [cells_size csize Nat.add] in ST'.
  tk_post. split; [tk_ms|]. split; [rewrite unsigned_lit by lia; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact ST'|]. split; [exact CQ | exact CB].
Qed.
