(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ge_achain adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACf5.v (rt_chain) for the call chain of libreac/fuzz_grant's entry function; the rest of the file is written for fuzz_grant's entry walk. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySeat.v, with its module paths and module names changed; 700 of its 746 lines of code are new or changed and 885 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/B/Prog/BoxBLxCase3SegA.v; 500 of its 589 lines of code are new or changed and 657 lines of the source are left out. *)
(* The walk of fuzz_boxreg.asan-ubsan's LLVMFuzzerTestOneInput, case 3 of a loop turn (op & 3 = 3; fuzz_boxreg.c
   case 3, `rename`): from the cut LI_T (0x8034c) to the cut LI_K (0x80b08) (BoxBLxDefs.v).
   The code (offsets from 0x7ffac in the listing):
   - 0x8034c .. 0x803d0: the switch: op & 3 = 3 goes to 0x804d0;
   - 0x804d0 .. 0x80504: idx = fuzz_u8 (&in), inlined: when in.n = 0 the byte is 0 (0x8081c), else the cursor
     advances by one and the byte at the old p is read after the shadow check of p (the input block's shadow);
   - 0x80820 .. 0x80824: name = read_name (&in) (BoxBReadName.v, caller-journal form: the cursor is in this frame);
   - 0x80828 .. 0x8084c: reac_boxreg_set_name (r, (int8) idx, op & 8 ? NULL : name) (BoxBReacBoxregSetName.v);
   - 0x80850 .. 0x80864: renamed = 0 <= idx < n ? idx : -1 (n = r->n before the call, s10);
   - renamed >= 0: the UBSan checks idx <= 4 and r + 56 * idx in range, then
     strncmp (r->box[idx].name, op & 8 ? "" : name, 31) (0x808a4, StrncmpDefB.v); a nonzero answer goes to abort,
     which set_name's post refutes (the field holds firstn 31 s and its NUL);
   - 0x808b0 .. 0x808b4: free (name) (YC5d.v afree04_rule);
   - 0x808b8 .. 0x808c0: s8 = renamed as an unsigned 32-bit value, then 0x80b08.
   The memory model is Pau's plain one (lib/Prog/Boxreg.v, lib/Prog/LLVMFuzzerTestOneInput_case3.v nu_inv, c3_ren),
   used as it is. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0s YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaRun PaShadow PaJournal BoxBase BoxRo BoxTailVis.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBSyms BoxBList BoxBPa BoxBPaLib BoxBFrame.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBCJ YC1g YC1h YC85.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBReacBoxregInit BoxBReadName BoxBReacBoxregSetName.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Rt Require Import StrncmpDefB SnprintfDefB.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBLxDefs BoxBLxSeat.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg BoxregUpd printf_facts_c read_name_c.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require LLVMFuzzerTestOneInput_inv LLVMFuzzerTestOneInput_case3.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Mem.
(* a Theorem Labs lane's amem8_of_high (lib/A/Rt/FMsnprintfSx.v; c3_name_ok's +8 slack of the heap name, R2). Required, not
   imported: named fully. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require FMsnprintfSx.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* An imported tactic file switches off lia's treatment of / and mod (lib/A/Prog/YC4b.v:23); this file wants it, for itself only. *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* ---- the model: the name as a C string, the field set_name writes, and what the turn keeps ---- *)

(* The C string of the bytes l: the bytes before the first NUL. *)
Fixpoint c3_cstr (l : list byte) : list Z :=
  match l with
  | [] => []
  | b :: t => if bv_unsigned b =? 0 then [] else bv_unsigned b :: c3_cstr t
  end.

Lemma c3_cstr_len : forall l, (length (c3_cstr l) <= length l)%nat.
Proof.
  induction l as [|b t IH]; cbn [c3_cstr length]; [lia|].
  destruct (bv_unsigned b =? 0); cbn [length]; lia.
Qed.

Lemma c3_cstr_pos : forall l, Forall (fun c => 0 < c < 256) (c3_cstr l).
Proof.
  induction l as [|b t IH]; cbn [c3_cstr]; [constructor|].
  destruct (Z.eqb_spec (bv_unsigned b) 0) as [_|Hb]; [constructor|].
  constructor; [|exact IH].
  pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr. lia.
Qed.

(* The string and its NUL are the first bytes of l ++ [0]. *)
Lemma c3_cstr_app0 : forall l i, (i <= length (c3_cstr l))%nat ->
  nth i (c3_cstr l ++ [0]) 0 = bv_unsigned (nth i (l ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)).
Proof.
  induction l as [|b t IH]; intros i Hi; cbn [c3_cstr length] in *.
  - assert (i = 0%nat) by lia. subst i. reflexivity.
  - destruct (Z.eqb_spec (bv_unsigned b) 0) as [Hb|Hb]; cbn [length] in Hi.
    + assert (i = 0%nat) by lia. subst i. cbn [nth app]. symmetry. exact Hb.
    + destruct i as [|i]; cbn [nth app]; [reflexivity|]. apply IH. lia.
Qed.

(* upd_bytes with a shorter piece is upd_bytes with the whole 32-byte field (its tail kept). *)
Lemma c3_upd_pad : forall (cs P : list byte) k, (k + 32 <= length cs)%nat -> (length P <= 32)%nat ->
  Mem.upd_bytes cs k P = Mem.upd_bytes cs k (P ++ firstn (32 - length P) (skipn (k + length P) cs)).
Proof.
  intros cs P k Hk HP. unfold Mem.upd_bytes.
  rewrite length_app, length_firstn, length_skipn.
  replace (k + (length P + Init.Nat.min (32 - length P) (length cs - (k + length P))))%nat with (k + 32)%nat by lia.
  rewrite <- app_assoc. f_equal. f_equal.
  rewrite <- (firstn_skipn (32 - length P) (skipn (k + length P) cs)) at 1.
  f_equal. rewrite skipn_skipn. f_equal. lia.
Qed.

(* The bytes set_name writes into the name field: firstn 31 s and the NUL. *)
Definition c3_fld (s : list Z) : list byte := printf_facts_c.pf_bytes (firstn 31 s ++ [0]).

Lemma c3_fld_len : forall s, (length (c3_fld s) <= 32)%nat.
Proof.
  intros s. unfold c3_fld, printf_facts_c.pf_bytes. rewrite length_map, length_app, length_firstn. cbn [length]. lia.
Qed.

Lemma c3_fld_nul : forall s, In (Z_to_bv 8 0) (c3_fld s).
Proof.
  intros s. unfold c3_fld, printf_facts_c.pf_bytes. rewrite map_app. apply in_or_app. right. left. reflexivity.
Qed.

(* renamed: the row set_name renamed, or -1 (0x80850 .. 0x80864). *)
Definition c3_ren (x n : Z) : Z := LLVMFuzzerTestOneInput_case3.c3_ren x n.

(* What set_name's bytes keep: the table's checks, the fabric, and every row but the renamed one's name. *)
Lemma c3_set_name_inv : forall bs idx s, Boxreg.boxreg_inv bs ->
  let bs' := tbreac_boxreg_set_name_bytes bs idx s in
  Boxreg.boxreg_inv bs' /\ Boxreg.bx_fabric bs' = Boxreg.bx_fabric bs /\
  lkept bs bs' (c3_ren idx (Boxreg.bx_n bs)) /\ -1 <= c3_ren idx (Boxreg.bx_n bs) < Boxreg.bx_n bs.
Proof.
  intros bs idx s HI bs'. subst bs'.
  pose proof HI as ((HL & H1 & _) & _). unfold Boxreg.boxreg_B1 in H1.
  unfold tbreac_boxreg_set_name_bytes, c3_ren, LLVMFuzzerTestOneInput_case3.c3_ren.
  destruct (Z.ltb_spec idx 0) as [Hlt | Hge]; cbn [orb].
  - replace (0 <=? idx) with false by (symmetry; apply Z.leb_gt; lia). cbn [andb].
    split; [exact HI|]. split; [reflexivity|]. split; [|lia].
    intros j Hj. repeat split; right; reflexivity.
  - destruct (Z.leb_spec (Boxreg.bx_n bs) idx) as [Hn | Hn].
    + replace (idx <? Boxreg.bx_n bs) with false by (symmetry; apply Z.ltb_ge; lia).
      rewrite andb_false_r.
      split; [exact HI|]. split; [reflexivity|]. split; [|lia].
      intros j Hj. repeat split; right; reflexivity.
    + replace (0 <=? idx) with true by (symmetry; apply Z.leb_le; lia).
      replace (idx <? Boxreg.bx_n bs) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb].
      rewrite (c3_upd_pad bs (c3_fld s)) by (pose proof (c3_fld_len s); lia).
      set (X := c3_fld s ++ firstn (32 - length (c3_fld s)) (skipn (Z.to_nat (56 * idx + 24) + length (c3_fld s)) bs)).
      assert (HX : length X = 32%nat).
      { subst X. rewrite length_app, length_firstn, length_skipn. pose proof (c3_fld_len s). lia. }
      assert (H0 : In (Z_to_bv 8 0) X) by (subst X; apply in_or_app; left; apply c3_fld_nul).
      destruct (LLVMFuzzerTestOneInput_case3.nu_inv bs X idx HI ltac:(lia) HX H0) as (Hi' & Hf' & Hk').
      split; [exact Hi'|]. split; [exact Hf'|]. split; [exact Hk'|lia].
Qed.

(* The renamed row's name field after set_name: the bytes of firstn 31 s and its NUL. *)
Lemma c3_set_name_fld : forall bs idx (s : list Z) j, Boxreg.boxreg_inv bs -> 0 <= idx < Boxreg.bx_n bs ->
  (j < length (firstn 31 s ++ [0%Z]))%nat ->
  nth (Z.to_nat (56 * idx + 24) + j) (tbreac_boxreg_set_name_bytes bs idx s) (Z_to_bv 8 0) =
  Z_to_bv 8 (nth j (firstn 31 s ++ [0]) 0).
Proof.
  intros bs idx s j HI Hidx Hj.
  pose proof HI as ((HL & H1 & _) & _). unfold Boxreg.boxreg_B1 in H1.
  unfold tbreac_boxreg_set_name_bytes.
  replace ((idx <? 0) || (Boxreg.bx_n bs <=? idx)) with false
    by (symmetry; apply orb_false_iff; split; [apply Z.ltb_ge | apply Z.leb_gt]; lia).
  unfold Mem.upd_bytes.
  rewrite app_nth2 by (rewrite length_firstn; lia). rewrite length_firstn.
  replace (Z.to_nat (56 * idx + 24) + j - Init.Nat.min (Z.to_nat (56 * idx + 24)) (length bs))%nat with j by lia.
  assert (Hj' : (j < length (printf_facts_c.pf_bytes (firstn 31 s ++ [0%Z])))%nat)
    by (unfold printf_facts_c.pf_bytes; rewrite length_map; exact Hj).
  rewrite app_nth1 by exact Hj'.
  unfold printf_facts_c.pf_bytes. apply map_nth.
Qed.

(* strncmp (field, s, 31) = 0: the field holds firstn 31 s and its NUL. *)
Lemma c3_strn_eq : forall s, abfm_strn_eq 31 (firstn 31 s) s.
Proof.
  intros s. unfold abfm_strn_eq. rewrite !firstn_app, firstn_firstn, length_firstn.
  replace (Init.Nat.min 31 31) with 31%nat by reflexivity. f_equal. f_equal. lia.
Qed.

Lemma c3_pw_in : forall {X} (R : X -> X -> Prop) l x y, pairwise R l -> In x l -> In y l -> x <> y -> R x y \/ R y x.
Proof.
  intros X R l. induction l as [|z l IH]; intros x y H Hx Hy Hne; [destruct Hx|].
  cbn [pairwise] in H. destruct H as [Hf Hp]. rewrite Forall_forall in Hf.
  destruct Hx as [<- | Hx]; destruct Hy as [<- | Hy].
  - exfalso. apply Hne. reflexivity.
  - left. exact (Hf y Hy).
  - right. exact (Hf x Hx).
  - exact (IH x y Hp Hx Hy Hne).
Qed.

Lemma c3_req : forall n, 0 < n -> req_size n = n.
Proof. intros n Hn. unfold req_size. destruct (Z.eqb_spec n 0); lia. Qed.

(* A request of at most 48 bytes is served by the primary allocator. *)
Lemma c3_from_primary : forall n, 0 <= n <= 48 -> from_primary n = true.
Proof.
  intros n Hn.
  assert (H : forallb (fun z => from_primary z) (map Z.of_nat (seq 0 49)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. apply H. apply in_map_iff. exists (Z.to_nat n). split; [lia|]. apply in_seq. lia.
Qed.

(* ---- what the calls of case 3 need, from the cut's facts and AR ---- *)
Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg boxb_listing}.
#[local] Notation SEGS := (@pa_segs _ boxb_listing PI).
#[local] Notation VAL := (@pa_val _ boxb_listing PI).
#[local] Notation BASE := (@pa_val _ boxb_listing PI A_TEXT).
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis HY : lx_hyps B MT.
Let LAWS : AR_laws SEGS B := lh_laws B MT HY.

(* A byte the reader shows, as the one-byte val_mem the runtime contracts read. *)
Lemma c3_val_mem1 : forall (W : world SEGS) mem a v, aview SEGS (w_H W) mem a = Some v ->
  val_mem SEGS (mrestrict (w_H W) mem) a 1 v /\ 0 <= v < 256.
Proof.
  intros W mem a v H. unfold aview in H.
  destruct (mbyte SEGS (mrestrict (w_H W) mem) a) as [b|] eqn:Hm; [|discriminate H].
  cbn [option_map] in H. injection H as <-.
  pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr.
  split; [|lia].
  intros k Hk. assert (k = 0%nat) by lia. subst k. replace (a + Z.of_nat 0) with a by lia. rewrite Hm. f_equal.
  rewrite le_byte_small by (cbn; lia). replace (8 * Z.of_nat 0) with 0 by reflexivity. rewrite Z.shiftr_0_r.
  symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* The caller's input bytes, from the cut's garr8. *)
Lemma c3_garr8_view : forall (W : world SEGS) mem p (l : list byte) i,
  garr8 SEGS (mrestrict (w_H W) mem) p (map (fun b : byte => bv_unsigned b) l) -> 0 <= i < Z.of_nat (length l) ->
  aview SEGS (w_H W) mem (p + i) = Some (bv_unsigned (nth (Z.to_nat i) l (Z_to_bv 8 0))).
Proof.
  intros W mem p l i Hg Hi. destruct (Hg (Z.to_nat i) ltac:(rewrite length_map; lia)) as [Hv Hb].
  rewrite Z2Nat.id in Hv by lia.
  assert (E : nth (Z.to_nat i) (map (fun b : byte => bv_unsigned b) l) 0 = bv_unsigned (nth (Z.to_nat i) l (Z_to_bv 8 0))).
  { rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0 : byte))) by (rewrite length_map; lia). apply map_nth. }
  rewrite E in Hv, Hb. apply aview_of_val_mem1; assumption.
Qed.

(* The machine stack's shadow is zero (AR's zero-shadow law over the layout's stack range). *)
Lemma c3_stk_ra : forall ly S (W : world SEGS) mem md a n, AR SEGS B ly S W mem md ->
  ly_stk_lo ly <= a -> a + n <= ly_stk_hi ly -> range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF a n.
Proof.
  intros ly S W mem md a n HAR Hlo Hhi x Hx.
  pose proof HAR as (M & _). pose proof (am_layout _ _ _ _ M) as LO.
  pose proof (lo_top _ LO) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). unfold page_aligned in T5, T6.
  pose proof (al_zshadow _ _ LAWS ly S W mem md (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) HAR
    (or_introl eq_refl)) as Z0.
  cbn [fst snd] in Z0.
  exists 0. split; [|left; reflexivity].
  pose proof (Z.div_mod (ly_stk_lo ly) 4096 ltac:(lia)) as D1.
  pose proof (Z.div_mod (ly_stk_hi ly) 4096 ltac:(lia)) as D2.
  pose proof (Z.div_mod x 8 ltac:(lia)) as D3. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as D4.
  rewrite T5, Z.add_0_r in D1. rewrite T6, Z.add_0_r in D2.
  set (ql := ly_stk_lo ly / 4096) in *. set (qh := ly_stk_hi ly / 4096) in *.
  assert (E1 : ly_stk_lo ly / 8 = 512 * ql) by (rewrite D1; replace (4096 * ql) with ((512 * ql) * 8) by lia; apply Z.div_mul; lia).
  assert (E2 : (ly_stk_hi ly - ly_stk_lo ly) / 8 = 512 * (qh - ql))
    by (rewrite D1, D2; replace (4096 * qh - 4096 * ql) with ((512 * (qh - ql)) * 8) by lia; apply Z.div_mul; lia).
  specialize (Z0 (x / 8 - 512 * ql)). rewrite E2 in Z0.
  unfold shadow_of_addr in Z0 |- *. rewrite E1 in Z0.
  replace (SHADOW_OFF + 512 * ql + (x / 8 - 512 * ql)) with (SHADOW_OFF + x / 8) in Z0 by lia.
  apply Z0. lia.
Qed.

(* A byte of the caller's stack window: the caller's journal may let a callee write it. *)
Lemma c3_stack_win : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k a,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  sp0 - STK <= a < sp0 ->
  awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) memc a /\
  ~ aowned B lyc Sc a /\ ly_stk_lo lyc <= a < ly_stk_hi lyc.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k a HJ Ha.
  pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & _).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
  assert (Hs : ly_stk_lo lyc <= a < ly_stk_hi lyc) by lia.
  split; [left; exact Ha|]. split; [exact (Hpres a Ha)|]. split; [|exact Hs].
  exact (al_stack _ _ LAWS lyc Sc W memc mdc a HAR Hs).
Qed.

(* A block of at most 48 bytes is a primary chunk: high memory, far below the ceiling. *)
Lemma c3_small_blk : forall ly S (W : world SEGS) mem md p n, AR SEGS B ly S W mem md ->
  In (p, n) (ablocks B ly S) -> 0 <= n <= 48 -> kHighMemBeg <= p /\ p + n + 4096 <= alloc_ceiling.
Proof.
  intros ly S W mem md p n HAR Hin Hn. pose proof HAR as (M & _).
  apply (proj1 (In_ablocks B ly S p n)) in Hin as (k & Hk & Hst & Hu & Hr).
  pose proof (chunk_facts B ly S _ k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
  pose proof (am_layout _ _ _ _ M) as LO.
  pose proof (req_size_pos (ck_req k) ltac:(lia)) as [Q1 Q2].
  destruct (ck_beg k) as [|off|r o|c q]; try solve [destruct GG].
  - cbv zeta in GG. destruct GG as (Gc & Gfp & _ & Gext & Gbase & Gx & _ & Gxs & Gal).
    pose proof (region_in_prim ly (prim_class off) LO ltac:(lia)) as (R1 & R2 & R3 & R4 & R5).
    unfold ASAN_CEIL in *. lia.
  - destruct GG as (_ & Gfp & _). rewrite Hr, (c3_from_primary n Hn) in Gfp. discriminate.
Qed.

(* The room read_name's malloc needs: one event, 48 bytes of live heap, and the meter for the request. *)
Lemma c3_room : forall cx fp k acc ly3 S3 (W3 : world SEGS) mem3 md3 r (i : nat) n,
  lx_base B MT cx ->
  ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
    [(LX_CID, fp)] ly3 S3 W3 mem3 md3 k ->
  mo_le MT (lc_S cx) S3 acc -> lblk B cx ly3 S3 r ->
  k <= 1 + 2 * Z.of_nat i -> (i < 64)%nat -> acc <= LX_A1 MT + Z.of_nat i * LX_AI MT -> 0 <= n <= 48 ->
  st_nev S3 + 1 <= EV_MAX /\ blocks_bytes S3 + 48 <= LIVE_MAX /\ mo_ok MT S3 (mo_malloc MT n) /\
  acc + mo_malloc MT n <= LX_A1 MT + (Z.of_nat i + 1) * LX_AI MT.
Proof.
  intros cx fp k acc ly3 S3 W3 mem3 md3 r i n HB HJ HLE HBL Hk Hi Hacc Hn.
  pose proof HB as (_ & _ & _ & _ & _ & _ & Hnev & Hbb & _ & Hok & Hneed & _).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev3 & _).
  pose proof (lh_mtl B MT HY) as ML.
  pose proof (mo_malloc_mono MT ML n 48 ltac:(lia)) as Mm.
  pose proof (mo_malloc_nonneg MT ML n ltac:(lia)) as Mn.
  pose proof (mo_malloc_nonneg MT ML 48 ltac:(lia)) as Mn48.
  pose proof (mo_free_nonneg MT ML) as Mf.
  assert (Hai : 0 <= LX_AI MT) by (unfold LX_AI; lia).
  assert (Hm : (Z.of_nat i + 1) * LX_AI MT <= 64 * LX_AI MT) by (apply Z.mul_le_mono_nonneg_r; lia).
  assert (Hacc' : acc + mo_malloc MT n <= LX_A1 MT + (Z.of_nat i + 1) * LX_AI MT) by (unfold LX_AI in *; lia).
  split; [unfold LX_EV in Hnev; lia|].
  split.
  - rewrite (blocks_bytes_bsum B ly3 S3). unfold lblk in HBL. rewrite HBL, bsum_app.
    rewrite <- (blocks_bytes_bsum B (lc_ly cx) (lc_S cx)). cbn [bsum fold_right fst snd].
    unfold LX_REG, LX_LIVE, LIVE_MAX in *. lia.
  - split; [|exact Hacc'].
    apply (mok_station MT (lc_S cx) S3 (lc_T cx) acc (mo_malloc MT n) ML Hok HLE Mn).
    unfold LX_NEED, LX_AI in *. lia.
Qed.

(* The name: set_name's premise on a heap name (the string before the name's first NUL). *)
Lemma c3_name_ok : forall ly S (W : world SEGS) mem md sp r q (nm : list byte),
  AR SEGS B ly S W mem md ->
  In (q, Z.of_nat (length nm) + 1) (ablocks B ly S) -> In (r, LX_REG) (ablocks B ly S) ->
  Z.of_nat (length nm) <= 47 ->
  (forall j, 0 <= j <= Z.of_nat (length nm) ->
     aview SEGS (w_H W) mem (q + j) = Some (bv_unsigned (nth (Z.to_nat j) (nm ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)))) ->
  alloc_ceiling + 8 <= sp - REAC_BOXREG_SET_NAME_STKB ->
  tbreac_boxreg_set_name_name_ok W mem sp r q (c3_cstr nm).
Proof.
  intros ly S W mem md sp r q nm HAR Hq Hr HL Hbytes Hsp.
  right. set (s := c3_cstr nm) in *. set (L := Z.of_nat (length nm)) in *.
  pose proof (c3_cstr_len nm) as Hsl. fold s in Hsl. pose proof (c3_cstr_pos nm) as Hpos. fold s in Hpos.
  assert (HsL : Z.of_nat (length s) <= L) by (subst L; lia).
  destruct (al_blocks _ _ LAWS ly S W mem md q (L + 1) HAR Hq) as (Hq16 & Hq4096 & Hqceil & Hqia & Hqp & Hpw & _).
  destruct (al_blocks _ _ LAWS ly S W mem md r LX_REG HAR Hr) as (Hr16 & Hr4096 & Hrceil & _).
  rewrite c3_req in Hqceil, Hqia by lia. change (req_size LX_REG) with 288 in Hrceil.
  assert (Hd : q + (L + 1) <= r \/ r + 288 <= q).
  { assert (Hne : (q, req_size (L + 1)) <> (r, req_size LX_REG)).
    { intros E. injection E as _ E2. rewrite c3_req in E2 by lia. change (req_size LX_REG) with 288 in E2. lia. }
    destruct (c3_pw_in zdisjoint _ (q, req_size (L + 1)) (r, req_size LX_REG) Hpw
      (in_map (fun b : Z * Z => (fst b, req_size (snd b))) _ _ Hq)
      (in_map (fun b : Z * Z => (fst b, req_size (snd b))) _ _ Hr) Hne) as [Hz | Hz];
      unfold zdisjoint in Hz; cbn [fst snd] in Hz; rewrite (c3_req (L + 1)) in Hz by lia;
      change (req_size LX_REG) with 288 in Hz; lia. }
  pose proof (Z.div_mod q 16 ltac:(lia)) as Dq. rewrite Hq16, Z.add_0_r in Dq.
  pose proof (Z.div_mod r 16 ltac:(lia)) as Dr. rewrite Hr16, Z.add_0_r in Dr.
  pose proof (Z.div_mod (Z.of_nat (length s)) 8 ltac:(lia)) as Ds. pose proof (Z.mod_pos_bound (Z.of_nat (length s)) 8 ltac:(lia)) as Dsb.
  assert (Hwe : absn_word_end q (Z.of_nat (length s)) = q + 8 * (Z.of_nat (length s) / 8) + 8).
  { unfold absn_word_end. rewrite Dq. replace (16 * (q / 16) + Z.of_nat (length s)) with
      (Z.of_nat (length s) + (2 * (q / 16)) * 8) by lia. rewrite Z.mod_add by lia. lia. }
  pose proof (Z.div_mod (L + 1 + 8 - 1) 8 ltac:(lia)) as Dl. pose proof (Z.mod_pos_bound (L + 1 + 8 - 1) 8 ltac:(lia)) as Dlb.
  assert (Hwe2 : 8 * (Z.of_nat (length s) / 8) + 8 <= (L + 1 + 8 - 1) / 8 * 8) by lia.
  split; [lia|]. split; [exact Hpos|]. split; [lia|].
  split.
  { intros i Hi. rewrite (Hbytes i) by lia. f_equal. symmetry. apply c3_cstr_app0. fold s. lia. }
  split.
  { intros a Ha. rewrite Hwe in Ha. destruct (Z_le_gt_dec a (q + L)) as [Hin | Hout].
    - replace a with (q + (a - q)) by lia. rewrite Hbytes by lia. discriminate.
    - apply (absn_blk_tail_vis_ok SEGS B ly S W mem md q (L + 1) a HAR Hq). unfold round_up. lia. }
  (* R2: set_name's amem_range q (|s| + 8): a block of at most 48 bytes is high and 4096 bytes below the ceiling *)
  split; [destruct (c3_small_blk ly S W mem md q (L + 1) HAR Hq ltac:(lia)) as [Hh Hm];
          apply FMsnprintfSx.amem8_of_high; [exact Hh | lia]|].
  split; [intros a Ha Hw; rewrite Hwe in Ha; unfold REAC_BOXREG_SET_NAME_STKB in *; lia|].
  split; [rewrite Hwe; unfold REG_SIZEB; lia|].
  split.
  - apply (range_addressable_of_block SEGS B LAWS ly S W mem md q (L + 1)); [exact HAR | exact Hq | lia | rewrite c3_req by lia; lia].
  - apply (shadow_hull_vis_of_block SEGS B LAWS ly S W mem md q (L + 1)); [exact HAR | exact Hq | lia | rewrite c3_req by lia; lia | lia].
Qed.

(* The name as strncmp's second string (op & 8 = 0). *)
Lemma c3_cstr_ok_name : forall ly S (W : world SEGS) mem md q (nm : list byte),
  AR SEGS B ly S W mem md -> In (q, Z.of_nat (length nm) + 1) (ablocks B ly S) -> Z.of_nat (length nm) <= 47 ->
  (forall j, 0 <= j <= Z.of_nat (length nm) ->
     aview SEGS (w_H W) mem (q + j) = Some (bv_unsigned (nth (Z.to_nat j) (nm ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)))) ->
  abfm_cstr_ok SEGS W mem q (c3_cstr nm).
Proof.
  intros ly S W mem md q nm HAR Hq HL Hbytes.
  set (s := c3_cstr nm) in *. set (L := Z.of_nat (length nm)) in *.
  pose proof (c3_cstr_len nm) as Hsl. fold s in Hsl. pose proof (c3_cstr_pos nm) as Hpos. fold s in Hpos.
  assert (HsL : Z.of_nat (length s) <= L) by (subst L; lia).
  destruct (al_blocks _ _ LAWS ly S W mem md q (L + 1) HAR Hq) as (Hq16 & Hq4096 & Hqceil & Hqia & _).
  rewrite c3_req in Hqceil, Hqia by lia.
  destruct (c3_small_blk ly S W mem md q (L + 1) HAR Hq ltac:(lia)) as [Hhm Hsm].
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (Z.div_mod q 16 ltac:(lia)) as Dq. rewrite Hq16, Z.add_0_r in Dq.
  pose proof (Z.div_mod (Z.of_nat (length s)) 8 ltac:(lia)) as Ds. pose proof (Z.mod_pos_bound (Z.of_nat (length s)) 8 ltac:(lia)) as Dsb.
  assert (Hwe : q + Z.of_nat (length s) - (q + Z.of_nat (length s)) mod 8 + 8 = q + 8 * (Z.of_nat (length s) / 8) + 8).
  { rewrite Dq. replace (16 * (q / 16) + Z.of_nat (length s)) with
      (Z.of_nat (length s) + (2 * (q / 16)) * 8) by lia. rewrite Z.mod_add by lia. lia. }
  pose proof (Z.div_mod (L + 1 + 8 - 1) 8 ltac:(lia)) as Dl. pose proof (Z.mod_pos_bound (L + 1 + 8 - 1) 8 ltac:(lia)) as Dlb.
  split; [split|].
  - intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
    pose proof (Hbytes (Z.of_nat j) ltac:(lia)) as Hb. rewrite Nat2Z.id in Hb.
    rewrite <- (c3_cstr_app0 nm j) in Hb by (fold s; lia). fold s in Hb.
    exact (c3_val_mem1 W mem (q + Z.of_nat j) _ Hb).
  - eapply Forall_impl; [|exact Hpos]. intros c Hc. cbv beta in Hc. lia.
  - split; [lia|]. split; [unfold ASAN_CEIL; lia|]. split; [lia|].
    split; [right; unfold kHighMemEnd, ASAN_CEIL in *; pose proof ASAN_CEIL_range as [CR _]; unfold ASAN_CEIL in CR; lia|].
    split; [apply (range_addressable_of_block SEGS B LAWS ly S W mem md q (L + 1)); [exact HAR | exact Hq | lia | rewrite c3_req by lia; lia]|].
    split; [apply (shadow_hull_vis_of_block SEGS B LAWS ly S W mem md q (L + 1)); [exact HAR | exact Hq | lia | rewrite c3_req by lia; lia | lia]|].
    intros a Ha. rewrite Hwe in Ha. destruct (Z_le_gt_dec a (q + L)) as [Hin | Hout].
    + replace a with (q + (a - q)) by lia. rewrite Hbytes by lia. discriminate.
    + apply (absn_blk_tail_vis_ok SEGS B ly S W mem md q (L + 1) a HAR Hq). unfold round_up. lia.
Qed.

(* The renamed row's name field as strncmp's first string. *)
Lemma c3_cstr_ok_fld : forall ly S (W : world SEGS) mem md r idx (s : list Z),
  AR SEGS B ly S W mem md -> In (r, LX_REG) (ablocks B ly S) -> 0 <= idx <= 4 -> Forall (fun c => 0 < c < 256) s ->
  (forall j, (j < length (firstn 31 s ++ [0%Z]))%nat ->
     aview SEGS (w_H W) mem (r + 56 * idx + 24 + Z.of_nat j) = Some (nth j (firstn 31 s ++ [0]) 0)) ->
  (forall i, 0 <= i < LX_REG -> aview SEGS (w_H W) mem (r + i) <> None) ->
  abfm_cstr_ok SEGS W mem (r + 56 * idx + 24) (firstn 31 s).
Proof.
  intros ly S W mem md r idx s HAR Hr Hidx Hpos Hf Hall.
  destruct (al_blocks _ _ LAWS ly S W mem md r LX_REG HAR Hr) as (Hr16 & Hr4096 & Hrceil & Hria & _).
  change (req_size LX_REG) with 288 in Hrceil, Hria.
  assert (Hl : Z.of_nat (length (firstn 31 s)) <= 31) by (rewrite length_firstn; lia).
  pose proof (Z.mod_pos_bound (r + 56 * idx + 24 + Z.of_nat (length (firstn 31 s))) 8 ltac:(lia)) as Dm.
  split; [split|].
  - intros j Hj. destruct (c3_val_mem1 W mem _ _ (Hf j Hj)) as [Hv Hb]. split; [exact Hv | exact Hb].
  - rewrite <- (firstn_skipn 31 s) in Hpos. apply Forall_app in Hpos as [Hpos _].
    eapply Forall_impl; [|exact Hpos]. intros c Hc. cbv beta in Hc. lia.
  - split; [lia|]. split; [unfold ASAN_CEIL; lia|]. split; [lia|].
    split; [apply (amem_range_of_block SEGS B LAWS ly S W mem md r LX_REG); [exact HAR | exact Hr | lia | change (req_size LX_REG) with 288; lia]|].
    split; [apply (range_addressable_of_block SEGS B LAWS ly S W mem md r LX_REG); [exact HAR | exact Hr | lia | change (req_size LX_REG) with 288; lia]|].
    split; [apply (shadow_hull_vis_of_block SEGS B LAWS ly S W mem md r LX_REG); [exact HAR | exact Hr | lia | change (req_size LX_REG) with 288; lia | lia]|].
    intros a Ha. replace a with (r + (a - r)) by lia. apply Hall. unfold LX_REG. lia.
Qed.

End h.

Lemma c3_atoms_ok_app : forall E l1 l2, atoms_ok E l1 -> atoms_ok E l2 -> atoms_ok E (l1 ++ l2).
Proof.
  intros E l1. induction l1 as [|[n f] t IH]; intros l2 H1 H2; cbn [app atoms_ok] in *; [exact H2|].
  destruct H1 as [Hf Ht]. split; [exact Hf | exact (IH l2 Ht H2)].
Qed.

(* ---- segment A: LI_T (0x8034c) to the call of read_name (0x80824) ---- *)
Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg boxb_listing}.
#[local] Notation SEGS := (@pa_segs _ boxb_listing PI).
#[local] Notation VAL := (@pa_val _ boxb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ boxb_listing PI).
#[local] Notation BASE := (@pa_val _ boxb_listing PI A_TEXT).
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis HY : lx_hyps B MT.
Let LAWS : AR_laws SEGS B := lh_laws B MT HY.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).

Definition C3_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* The spill slots segment A reads or carries (lslots_loop, the frame slots, the cursor). *)
Definition c3A_l : list (Z * sv) :=
  [(0x08, SLit 3); (0x10, SOff LA_F 0); (0x18, SOff LA_F 0); (0x28, SOff 20 280); (0x30, SOff 27 0);
   (0x38, SLit 0); (0x40, SOff 50 0); (0x68, SOff LA_F 32); (0x70, SOff 51 0); (0x78, SOff 52 0);
   (0x80, SOff LA_F 0); (0x88, SOff 48 0); (0x90, SOff 49 0)].
Definition c3A_ov : list (bv 5 * sv) := LX_OVP ++ [((19%bv : bv 5), SLit 1)].
(* The idx byte the inlined fuzz_u8 reads at the cursor. *)
Definition c3A_byte : YP09.region := YP09.mkRegion (Some 48%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 53 0))].
Definition c3A_G : facts :=
  mkFacts (LX_AF ++ [(48%nat, mkAF 4096 0x7fffff800000 0); (49%nat, mkAF 1 (2 ^ 26) 0); (53%nat, mkAF 0 255 0)]) [] [].
(* The shadow entry: the idx byte (in the input block). The frame region is read-only (fwlo = fwhi = 0), so the
   shadow span needs no reverse entry for it. *)
Definition c3A_SH : list shent := [mkSHE 48 0 1].
(* The phase's atoms: 48 the cursor's p, 49 its n, 50 r->n's shadow byte address, 51 ~r, 52 ~prev, 53 the idx byte. *)
Definition c3A_ex (cx : lxcx) (fp r : Z) (pos : nat) : list word :=
  [w64 (lc_p cx + Z.of_nat (S pos)); w64 (lc_n cx - Z.of_nat (S pos)); w64 (shadow_addr (r + 280));
   w64 (2 ^ 64 - 1 - r); w64 (2 ^ 64 - 1 - (lF cx fp + 64));
   w64 (bv_unsigned (nth (S pos) (lc_pl cx) (Z_to_bv 8 0)))].

Lemma c3A_seat : forall cx fp k ly3 S3 W3 ms3 md3 pos r fab bs E,
  lx_base B MT cx ->
  ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
    [(LX_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [(LX_CID, fp)] ->
  lx_body cx fp LP_T W3 ms3 LSH_iter -> lblk B cx ly3 S3 r -> Boxreg.boxreg_inv bs -> Boxreg.bx_fabric bs = fab ->
  (S pos < length (lc_pl cx))%nat -> lcur cx W3 ms3 (S pos) -> lslots_loop cx fp W3 ms3 r fab ->
  getr (ms_regs ms3) 19 = w64 1 -> getr (ms_regs ms3) 20 = w64 r -> getr (ms_regs ms3) 21 = w64 (lF cx fp + 64) ->
  getr (ms_regs ms3) 27 = w64 fab ->
  E = lx_env cx fp (ms_regs ms3) (c3A_ex cx fp r pos) ->
  st_ok_pi SEGS VAL E (lx_ss LP_T (lx_sr c3A_ov) LSH_iter (lx_slot_chunks c3A_l) [] 0 0 0 0 [c3A_byte] c3A_G)
    (restrict (w_H W3) ms3) /\
  sh_ok SEGS (SOff LA_SB 0) c3A_SH E (mrestrict (w_H W3) (ms_mem ms3)).
Proof.
  intros cx fp k ly3 S3 W3 ms3 md3 pos r fab bs E HB HJ HFR HBD Hblk Hinv Hfab Hlen Hcur Hloop R19 R20 R21 R27 HEdef.
  pose proof HBD as (Hpc & Hrv & Hsvc & Hrom & Hfr & Hfc & HRG & HSV & HSH & HFL & S10 & S18 & S80 & HIN).
  pose proof (lx_sp_facts B MT cx HB) as (Hal16 & Hceil & H47 & Hsp1 & Hal32).
  pose proof (lx_F_facts B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR) as (HF0 & HFc & HFia & HFo & HF64 & HSHeq).
  pose proof HJ as (HAR3 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HB as (_ & _ & _ & Hpn & _).
  destruct Hpn as [Hn0 | (Hnpos & Hin0)]; [unfold lc_n in Hn0; lia|].
  assert (Hin3 : In (lc_p cx, lc_n cx) (ablocks B ly3 S3))
    by (unfold lblk in Hblk; rewrite Hblk; apply in_or_app; left; exact Hin0).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin3) as (Hp16 & Hp4096 & Hpceil & Hpia & _).
  rewrite (c3_req (lc_n cx)) in Hpceil, Hpia by lia.
  assert (Hlen' : Z.of_nat (S pos) < lc_n cx) by (unfold lc_n; lia).
  assert (Hrin : In (r, LX_REG) (ablocks B ly3 S3))
    by (unfold lblk in Hblk; rewrite Hblk; apply in_or_app; right; left; reflexivity).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hrin) as (Hr16 & Hr4096 & Hrceil & Hria & _).
  change (req_size LX_REG) with 288 in Hrceil, Hria.
  pose proof Hcur as (Hcl & H88 & H90).
  pose proof Hloop as (L08 & L28 & L30 & L38 & L40 & L68 & L70 & L78).
  pose proof Hinv as ((_ & _ & HB2 & _) & _). unfold Boxreg.boxreg_B2 in HB2.
  pose proof (bv_unsigned_in_range 8 (nth (S pos) (lc_pl cx) (Z_to_bv 8 0))) as Hb. change (bv_modulus 8) with 256 in Hb.
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ LX_CID fp HAR3 Hin3 (lx_fin fp S3 HFR)) as HdF.
  unfold zdisjoint in HdF. cbn [fst snd] in HdF.
  rewrite (lx_frame_addr_eq B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ), (c3_req (lc_n cx)) in HdF by lia.
  change (fs_frame_bytes LX_CID) with 512 in HdF.
  assert (HE : lx_E cx fp E) by (rewrite HEdef; apply lx_env_E; exact HRG).
  pose proof HE as (E2 & E8 & E3 & E4 & E22 & E32 & ESV & E46 & E47).
  assert (EX : forall j, (j < 6)%nat -> ew E (LA_EX + j) = nth j (c3A_ex cx fp r pos) (w64 0))
    by (intros j Hj; rewrite HEdef; apply lx_env_ex; unfold LA_EX; lia).
  pose proof (EX 0%nat ltac:(lia)) as E48. pose proof (EX 1%nat ltac:(lia)) as E49.
  pose proof (EX 2%nat ltac:(lia)) as E50. pose proof (EX 3%nat ltac:(lia)) as E51.
  pose proof (EX 4%nat ltac:(lia)) as E52. pose proof (EX 5%nat ltac:(lia)) as E53.
  cbn [nth c3A_ex LA_EX Nat.add] in E48, E49, E50, E51, E52, E53.
  assert (E20 : ew E 20 = w64 r)
    by (rewrite HEdef, (lx_env_reg cx fp (ms_regs ms3) (c3A_ex cx fp r pos) 20 (20%bv : bv 5)) by reflexivity; exact R20).
  assert (E27 : ew E 27 = w64 fab)
    by (rewrite HEdef, (lx_env_reg cx fp (ms_regs ms3) (c3A_ex cx fp r pos) 27 (27%bv : bv 5)) by reflexivity; exact R27).
  pose proof (lx_extents B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR E HE) as (X8 & X2 & X46 & X22).
  assert (Hshr : 0 <= shadow_addr (r + 280) < 2 ^ 64) by (unfold shadow_addr, SHADOW_OFF; lia).
  split.
  - apply (lx_seat B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR E LP_T (lx_sr c3A_ov) LSH_iter c3A_l [] 0 0 0 0
             [c3A_byte] c3A_G HE HBD).
    + apply lx_regs_ok; [rewrite HEdef; apply lx_regs_ok_atoms|]. unfold c3A_ov. apply Forall_app. split.
      * rewrite HEdef. apply lx_ovp_ok; [exact HRG | exact R21].
      * apply Forall_cons; [|apply Forall_nil]. cbn [fst snd sv_denot]. rewrite R19. reflexivity.
    + unfold c3A_l, lx_slots. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      * exact (lx_slot_lit cx W3 ms3 E 8 3 L08 ltac:(lia)).
      * apply (lx_slot_atom cx W3 ms3 E 16 LA_F (lF cx fp) 0); [rewrite Z.add_0_r; exact S10 | exact E46 | lia | lia].
      * apply (lx_slot_atom cx W3 ms3 E 24 LA_F (lF cx fp) 0); [rewrite Z.add_0_r; exact S18 | exact E46 | lia | lia].
      * apply (lx_slot_atom cx W3 ms3 E 40 20 r 280); [exact L28 | exact E20 | lia | lia].
      * apply (lx_slot_atom cx W3 ms3 E 48 27 fab 0); [rewrite Z.add_0_r; exact L30 | exact E27 | lia | lia].
      * exact (lx_slot_lit cx W3 ms3 E 56 0 L38 ltac:(lia)).
      * apply (lx_slot_atom cx W3 ms3 E 64 50 (shadow_addr (r + 280)) 0); [rewrite Z.add_0_r; exact L40 | exact E50 | lia | lia].
      * apply (lx_slot_atom cx W3 ms3 E 104 LA_F (lF cx fp) 32); [exact L68 | exact E46 | lia | lia].
      * apply (lx_slot_atom cx W3 ms3 E 112 51 (2 ^ 64 - 1 - r) 0); [rewrite Z.add_0_r; exact L70 | exact E51 | lia | lia].
      * apply (lx_slot_atom cx W3 ms3 E 120 52 (2 ^ 64 - 1 - (lF cx fp + 64)) 0);
          [rewrite Z.add_0_r; exact L78 | exact E52 | lia | lia].
      * apply (lx_slot_atom cx W3 ms3 E 128 LA_F (lF cx fp) 0); [rewrite Z.add_0_r; exact S80 | exact E46 | lia | lia].
      * apply (lx_slot_atom cx W3 ms3 E 136 48 (lc_p cx + Z.of_nat (S pos)) 0);
          [rewrite Z.add_0_r; exact H88 | exact E48 | unfold lc_n in *; lia | unfold lc_n in *; lia].
      * apply (lx_slot_atom cx W3 ms3 E 144 49 (lc_n cx - Z.of_nat (S pos)) 0);
          [rewrite Z.add_0_r; exact H90 | exact E49 | unfold lc_n in *; lia | unfold lc_n in *; lia].
    + apply Forall_nil.
    + lia.
    + lia.
    + lia.
    + lia.
    + vm_compute. reflexivity.
    + apply Forall_cons; [|apply Forall_nil]. unfold YP09.region_ok, c3A_byte.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
      rewrite E48. unfold w64. rewrite unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ (lc_p cx + Z.of_nat (S pos)) 0 1 (SOff 53 0)
               (bv_unsigned (nth (S pos) (lc_pl cx) (Z_to_bv 8 0)))).
      * rewrite lx_sv_SOff0, E53. reflexivity.
      * cbn. lia.
      * cbn. lia.
      * cbn [N.to_nat]. rewrite Z.add_0_r.
        pose proof (c3_garr8_view W3 (ms_mem ms3) (lc_p cx) (lc_pl cx) (Z.of_nat (S pos)) HIN ltac:(lia)) as Hv.
        rewrite Nat2Z.id in Hv. exact (proj1 (c3_val_mem1 W3 (ms_mem ms3) _ _ Hv)).
    + cbn [YP09.pairwise_disjoint YP09.all_disjoint]. tauto.
    + unfold lx_regions0. repeat apply Forall_cons; try apply Forall_nil;
        cbn [YP09.all_disjoint]; (split; [|exact I]); unfold YP09.extent_disjoint, c3A_byte, lx_saved_region,
        lx_spill_region, lx_frame_region, lx_shadow_region, fframe_region, fshadow_region;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi]; rewrite ?X8, ?X2, ?X46, ?X22;
        cbn [YP09.base_val]; rewrite E48; unfold w64; rewrite unsigned_lit_small by lia;
        change (fs_frame_bytes LX_CID) with 512; change (512 / 8) with 64;
        unfold in_app, LX_SPILL, SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *; lia.
    + unfold c3A_G. split; [|split; exact I]. cbn [f_atoms].
      apply c3_atoms_ok_app; [exact (lx_af_ok B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR E HE)|].
      cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E48, E49, E53. unfold w64.
      rewrite !unsigned_lit_small by (unfold lc_n in *; lia). rewrite Z.pow_0_r, !Z.mod_1_r.
      unfold lc_n in *. repeat match goal with |- _ /\ _ => split end; try exact I; lia.
  - unfold sh_ok, c3A_SH. apply Forall_cons; [|apply Forall_nil].
    apply (lx_shent_block B LAWS ly3 S3 W3 (ms_mem ms3) md3 E (lc_p cx + Z.of_nat (S pos)) (lc_p cx) (lc_n cx)
             0 1 48 HAR3 Hin3).
    + apply (U_atom E LA_SB SHADOW_OFF); [exact E32 | unfold SHADOW_OFF; lia].
    + apply (U_atom E 48 (lc_p cx + Z.of_nat (S pos))); [exact E48 | lia].
    + lia.
    + lia.
    + rewrite (c3_req (lc_n cx)) by lia. unfold lc_n in *. lia.
Qed.

(* ---- what a run leaves: its write rights, and the engine's state at a callee's entry ---- *)
(* Of the regions a phase of case 3 runs with, only the spill region has a write window, and it lies inside the
   machine frame's window [sp0 - LX_STK, sp0). *)
Lemma c3_awr_gen : forall E cx STK FP bl0 blc ly own rs,
  ew E 2 = w64 (lsp1 cx) -> 0 <= lsp1 cx -> lsp1 cx < 2 ^ 64 ->
  Forall (fun r => YP09.r_whi r <= YP09.r_wlo r \/
                   (YP09.r_base r = Some 2%nat /\ - STK <= lsp1 cx - lsp0 cx + YP09.r_wlo r
                    /\ lsp1 cx - lsp0 cx + YP09.r_whi r <= 0)) rs ->
  awr_ok E rs STK (lsp0 cx) FP bl0 blc ly own.
Proof.
  intros E cx STK FP bl0 blc ly own rs H2 H0 H1 HF.
  induction rs as [|x rs IH]; [apply awr_ok_nil|].
  inversion HF as [|y z Hx Ht]; subst.
  destruct Hx as [Hro | (Hb & Hlo & Hhi)].
  - apply awr_ok_cons_ro; [exact Hro | exact (IH Ht)].
  - eapply (awr_ok_cons_stack_off E x rs STK (lsp0 cx) FP bl0 blc ly own 2%nat (lsp1 cx - lsp0 cx));
      [exact Hb | | exact Hlo | exact Hhi | exact (IH Ht)].
    rewrite H2. unfold w64. rewrite unsigned_lit_small by lia. lia.
Qed.

(* The engine stops a call at `setpc ss (BASE + pc)`; the callee's walk wants the same state as st_ok_pi at pc. *)
Lemma c3_pi_of_st : forall E ss pc ms, st_ok SEGS E (setpc ss (BASE + pc)) ms -> st_ok_pi SEGS VAL E (setpc ss pc) ms.
Proof. intros E ss pc ms H. exact H. Qed.

(* ---- the points of case 3, one per call boundary ---- *)
(* 0x80828: read_name has returned (a0 = the name block). *)
Definition LP_RN : Z := 0x87c.
(* 0x80850: reac_boxreg_set_name has returned. *)
Definition LP_SN : Z := 0x8a4.
(* 0x808b0: the two paths (renamed, or not) meet; `mv a0, s3` and the call of free follow. *)
Definition LP_FREE : Z := 0x904.

Definition c3_nlen (nm : list byte) : Z := Z.of_nat (length nm).
(* The sign-extended index byte, the argument set_name gets (slli 0x38 / srai 0x38 at 0x8083c). *)
Definition c3_sext8 (b : Z) : Z := if b <? 128 then b else b - 256.
(* The name set_name is given: NULL and "" when op & 8 <> 0, else the heap name and its C string. *)
Definition c3_sel_q (op q : Z) : Z := if Z.land op 8 =? 0 then q else 0.
Definition c3_sel_s (op : Z) (nm : list byte) : list Z := if Z.land op 8 =? 0 then c3_cstr nm else [].

(* What every point of case 3 after read_name carries: the body, the budget, the two blocks, the registry's bytes,
   `prev`, the turn's slots and the registers the loop keeps. *)
Definition C3_body (pc : Z) (i : nat) (cx : lxcx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (pos : nat) (r fab op q : Z) (bs bsc nm : list byte) : Prop :=
  lx_body cx fp pc W3 ms3 LSH_iter /\ (i < 64)%nat /\
  k <= 2 + 2 * Z.of_nat i /\ acc <= LX_A1 MT + Z.of_nat i * LX_AI MT + mo_malloc MT (c3_nlen nm + 1) /\
  ablocks B ly3 S3 = ablocks B (lc_ly cx) (lc_S cx) ++ [(r, LX_REG); (q, c3_nlen nm + 1)] /\
  4096 <= q /\ c3_nlen nm <= 47 /\
  (forall j, 0 <= j <= c3_nlen nm ->
     lview W3 ms3 (q + j) = Some (bv_unsigned (nth (Z.to_nat j) (nm ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)))) /\
  lreg W3 ms3 r bsc /\ Boxreg.boxreg_inv bs /\ Boxreg.bx_fabric bs = fab /\ lprev cx fp W3 ms3 bs /\
  Z.land op 3 = 3 /\ 0 <= op < 256 /\
  lcur cx W3 ms3 pos /\ lslots_loop cx fp W3 ms3 r fab /\ lslot cx W3 ms3 0x58 (Z.of_nat i) /\
  getr (ms_regs ms3) 20 = w64 r /\ getr (ms_regs ms3) 21 = w64 (lF cx fp + 64) /\
  getr (ms_regs ms3) 26 = w64 (Boxreg.bx_n bs) /\ getr (ms_regs ms3) 27 = w64 fab.

(* 0x80828: read_name returned the name block q (its bytes nm and the NUL); s3 still 1, s7 the op byte, s8 the
   index byte, a0 the name. *)
Definition C3_RN (i : nat) : lxcx -> Z -> Z -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
  fun cx fp k acc ly3 S3 W3 ms3 md3 =>
  exists (pos : nat) (r fab op idxb q : Z) (bs nm : list byte),
  C3_body LP_RN i cx fp k acc ly3 S3 W3 ms3 pos r fab op q bs bs nm /\
  0 <= idxb < 256 /\
  getr (ms_regs ms3) 10 = w64 q /\ getr (ms_regs ms3) 19 = w64 1 /\
  getr (ms_regs ms3) 23 = w64 op /\ getr (ms_regs ms3) 24 = w64 idxb.

(* 0x80850: set_name has written the registry (bsc = its bytes); s3 = the name block, s7 the signed index,
   s8 the index byte (callee-saved across set_name; segment C's UBSan checks 0x80870 / 0x80884 and the strncmp field
   address read it), s9 = op & 8, s10 still the row count before the call. *)
Definition C3_SN (i : nat) : lxcx -> Z -> Z -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
  fun cx fp k acc ly3 S3 W3 ms3 md3 =>
  exists (pos : nat) (r fab op idxb q : Z) (bs nm : list byte),
  C3_body LP_SN i cx fp k acc ly3 S3 W3 ms3 pos r fab op q bs
    (tbreac_boxreg_set_name_bytes bs (c3_sext8 idxb) (c3_sel_s op nm)) nm /\
  0 <= idxb < 256 /\
  getr (ms_regs ms3) 19 = w64 q /\ getr (ms_regs ms3) 23 = w64 (c3_sext8 idxb) /\
  getr (ms_regs ms3) 24 = w64 idxb /\
  getr (ms_regs ms3) 25 = w64 (Z.land op 8).

(* 0x808b0: the renaming is decided (s7 = renamed, -1 when the row was not renamed) and, when it happened, the
   row's name field holds what set_name wrote; `mv a0, s3` and free (name) follow. *)
Definition C3_FREE (i : nat) : lxcx -> Z -> Z -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
  fun cx fp k acc ly3 S3 W3 ms3 md3 =>
  exists (pos : nat) (r fab op idxb q : Z) (bs nm : list byte),
  C3_body LP_FREE i cx fp k acc ly3 S3 W3 ms3 pos r fab op q bs
    (tbreac_boxreg_set_name_bytes bs (c3_sext8 idxb) (c3_sel_s op nm)) nm /\
  0 <= idxb < 256 /\
  getr (ms_regs ms3) 19 = w64 q /\
  getr (ms_regs ms3) 23 = w64 (c3_ren (c3_sext8 idxb) (Boxreg.bx_n bs)).

(* ---- the segments of case 3 ---- *)
(* 0x8034c .. 0x80824: the switch, the inlined fuzz_u8 for the index byte, the call of read_name. *)
Definition c3_segA_ok (POST : lxcx -> world SEGS -> config -> Prop) : Prop :=
  forall i, lx_from B MT POST (C3_RN i) -> lx_from B MT POST (LI_T B MT 3 i).
(* 0x80850 .. 0x808b0: renamed = 0 <= idx < n ? idx : -1, the UBSan checks and the strncmp of the row's name. *)
Definition c3_segC_ok (POST : lxcx -> world SEGS -> config -> Prop) : Prop :=
  forall i, lx_from B MT POST (C3_FREE i) -> lx_from B MT POST (C3_SN i).
(* 0x808b0 .. 0x80b08: free (name), s8 = renamed as an unsigned 32-bit value, the jump to the join. *)
Definition c3_segD_ok (POST : lxcx -> world SEGS -> config -> Prop) : Prop :=
  forall i, lx_from B MT POST (LI_K B MT i) -> lx_from B MT POST (C3_FREE i).

End w.

(* 0x80828 .. 0x8084c: the name argument, the sign-extended index, the call of reac_boxreg_set_name. The call may reach
   the snprintf wrapper, which returns at SOME FP state fx' (BoxBase.v apost_baseF, BoxBLxDefs.v lx_fxr), so the
   segment lands on C3_SN taken at every such fx' (a Theorem Labs lane's binding shape for a cross-call segment); stated outside
   Section w, whose C3_SN is pinned to the Section's fx. *)
Section wf. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg boxb_listing}.
#[local] Notation SEGS := (@pa_segs _ boxb_listing PI).
Variable B : asyms.
Variable MT : ameter_ops.
Definition c3_segB_ok (POST : lxcx -> world SEGS -> config -> Prop) : Prop :=
  forall i, Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
    (forall fx' : YK11.FPState, lx_fxr fx fx' -> lx_from B MT POST (C3_SN (fx := fx') B MT i)) ->
    lx_from B MT POST (C3_RN B MT i).
End wf.
