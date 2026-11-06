(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes SCPS Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import PImg CJ_iface CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_pstr_A.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pstr_A.CJ_print_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import CJ_pstr_A.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_pad F_printf_iface Printf_model.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= rewrite (unsigned_lit_wrap e).
Local Ltac zs_wrap_in e H ::= rewrite (unsigned_lit_wrap e) in H.
Local Ltac zs_idioms ::=
  match goal with
  | |- context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e)
  | |- context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e)
  | |- context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] => rewrite (zb_shl_shr x k) by (first [lia | zrange_nonneg])
  end.
Local Ltac zs_idioms_in H ::=
  match type of H with
  | context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e) in H
  | context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e) in H
  | context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] => rewrite (zb_shl_shr x k) in H by (first [lia | zrange_nonneg])
  end.

Ltac shh H := let T := type of H in idtac H ":" T.
Ltac shmem :=
  lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ ?m _) => idtac "PC" pc "MEM" m;
    repeat match goal with H : context [m] |- _ => shh H; revert H end end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma u8arr_split3 : forall m A bs (k n : nat),
  u8arr psegs m A bs -> (k + n <= length bs)%nat ->
  u8arr psegs m A (firstn k bs)
  /\ rw_cells psegs m (A + Z.of_nat k) [CB n (firstn n (skipn k bs))]
  /\ u8arr psegs m (A + Z.of_nat k + Z.of_nat n) (skipn (k + n) bs).
Proof.
  intros m A bs k n [BA WR] Hkn.
  rewrite <- (firstn_skipn k bs) in BA. apply bytes_at_app in BA. destruct BA as [BA1 BA2].
  rewrite firstn_length_le in BA2 by lia.
  rewrite <- (firstn_skipn n (skipn k bs)) in BA2. apply bytes_at_app in BA2. destruct BA2 as [BA2 BA3].
  rewrite firstn_length_le in BA3 by (rewrite skipn_length; lia). rewrite skipn_skipn in BA3.
  (nelim WR 3%nat; intros W0 W1 W).
  split; [|split].
  - split; [exact BA1|]. split; [lia|]. split; [rewrite firstn_length_le by lia; lia|]. intros i Hi. apply W. rewrite firstn_length_le in Hi by lia. lia.
  - split; [split; [cbn; rewrite firstn_length_le by (rewrite skipn_length; lia); auto|]|].
    + cbn [cells_bytes cbytes]. rewrite app_nil_r. exact BA2.
    + cbn [cells_size csize]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|]. intros i Hi.
      replace (A + Z.of_nat k + i) with (A + (Z.of_nat k + i)) by lia. apply W. lia.
  - split; [rewrite Nat.add_comm; exact BA3|]. split; [lia|]. rewrite skipn_length. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat k + Z.of_nat n + i) with (A + (Z.of_nat k + Z.of_nat n + i)) by lia. apply W. lia.
Qed.

Lemma u8arr_join3 : forall m A pre n mid suf,
  u8arr psegs m A pre -> rw_cells psegs m (A + Z.of_nat (length pre)) [CB n mid] -> u8arr psegs m (A + Z.of_nat (length pre) + Z.of_nat n) suf ->
  u8arr psegs m A (pre ++ mid ++ suf) /\ length mid = n.
Proof.
  intros m A pre n mid suf [B1 W1] RW [B3 W3].
  pose proof RW as [[Hwf B2] W2]. cbn in Hwf. destruct Hwf as [Ln _].
  cbn [cells_bytes cbytes] in B2. rewrite app_nil_r in B2. cbn [cells_size csize] in W2. rewrite Nat.add_0_r in W2.
  split; [|exact Ln]. split.
  - apply bytes_at_app. split; [exact B1|]. apply bytes_at_app. split; [exact B2|]. rewrite Ln. exact B3.
  - (nelim W1 3%nat; intros X0 X1 X). (nelim W2 3%nat; intros Y0 Y1 Y). (nelim W3 3%nat; intros Z0 Z1 ZZ).
    rewrite !length_app, Ln. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z_lt_le_dec i (Z.of_nat (length pre))); [apply X; lia|].
    destruct (Z_lt_le_dec i (Z.of_nat (length pre) + Z.of_nat n)).
    + replace (A + i) with (A + Z.of_nat (length pre) + (i - Z.of_nat (length pre))) by lia. apply Y. lia.
    + replace (A + i) with (A + Z.of_nat (length pre) + Z.of_nat n + (i - Z.of_nat (length pre) - Z.of_nat n)) by lia. apply ZZ. lia.
Qed.

Lemma u8arr_join3' : forall m A pre (k : Z) n mid suf,
  u8arr psegs m A pre -> Z.of_nat (length pre) = k -> rw_cells psegs m (A + k) [CB n mid] -> u8arr psegs m (A + k + Z.of_nat n) suf ->
  u8arr psegs m A (pre ++ mid ++ suf) /\ length mid = n.
Proof. intros m A pre k n mid suf H1 <- H2 H3. eapply u8arr_join3; eauto. Qed.

(* [comment removed for export] *)
Lemma u8_store : forall m A buf (k : Z) (b : byte),
  u8arr psegs m A buf -> 0 <= k < Z.of_nat (length buf) ->
  store_ok psegs m (wa (A + k)) 1 = true /\ u8arr psegs (write_to_mem m (wa (A + k)) [b]) A (upd buf (Z.to_nat k) b).
Proof.
  intros m A buf k b ARR Hk. split.
  - eapply u8arr_store_ok; [exact ARR| exact Hk| reflexivity].
  - apply u8arr_write; [exact ARR| exact Hk].
Qed.

Lemma u8_store' : forall m A buf (a k : Z) (b : byte),
  u8arr psegs m A buf -> a = A + k -> 0 <= k < Z.of_nat (length buf) ->
  store_ok psegs m (wa a) 1 = true /\ u8arr psegs (write_to_mem m (wa a) [b]) A (upd buf (Z.to_nat k) b).
Proof. intros m A buf a k b ARR -> Hk. apply u8_store; assumption. Qed.

Lemma le1_lit8 : forall z, 0 <= z < 256 -> le1 (Z_to_bv 64 z) = [Z_to_bv 8 z].
Proof. intros z Hz. unfold le1. cbn [Z_to_le_bytes]. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma esc_extra_plain : forall c, 32 <= c -> c <> 34 -> c <> 92 -> esc_extra c = 0.
Proof.
  intros c H1 H2 H3. unfold esc_extra.
  destruct (Z.eqb_spec c 34), (Z.eqb_spec c 92), (Z.eqb_spec c 8), (Z.eqb_spec c 12), (Z.eqb_spec c 10), (Z.eqb_spec c 13), (Z.eqb_spec c 9); cbn [orb]; try lia.
  destruct (Z.ltb_spec c 32); [lia| reflexivity].
Qed.

Lemma esc_extra_special : forall c, c < 32 \/ c = 34 \/ c = 92 -> 1 <= esc_extra c.
Proof.
  intros c H. unfold esc_extra. destruct (_ || _) eqn:EQ; [lia|].
  destruct (Z.ltb_spec c 32); [lia|]. exfalso.
  rewrite !Bool.orb_false_iff in EQ. destruct EQ as ((((((E1 & E2) & _) & _) & _) & _) & _).
  apply Z.eqb_neq in E1. apply Z.eqb_neq in E2. lia.
Qed.

Lemma land255 : forall c, 0 <= c < 256 -> Z.land c 255 = c.
Proof. intros c Hc. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

(* [comment removed for export] *)
Definition EJT : list byte := map wb
  [248; 62; 0; 0; 52; 63; 0; 0; 28; 63; 0; 0; 12; 63; 0; 0; 44; 63; 0; 0; 60; 63; 0; 0; 12; 63; 0; 0; 12; 63; 0; 0; 12; 63; 0; 0; 12; 63; 0; 0; 12; 63; 0; 0; 12; 63; 0; 0; 12; 63; 0; 0; 12; 63; 0; 0; 12; 63; 0; 0; 12; 63; 0; 0; 12; 63; 0; 0; 12; 63; 0; 0; 12; 63; 0; 0; 12; 63; 0; 0; 12; 63; 0; 0; 12; 63; 0; 0; 12; 63; 0; 0; 12; 63; 0; 0; 12; 63; 0; 0; 12; 63; 0; 0; 36; 63; 0; 0].

Definition ejt_sel (c : Z) : Z :=
  if c =? 8 then 0x3ef8 else if c =? 9 then 0x3f34 else if c =? 10 then 0x3f1c
  else if c =? 12 then 0x3f2c else if c =? 13 then 0x3f3c else if c =? 34 then 0x3f24 else 0x3f0c.

Lemma ejt_bytes : forall m, mem_inv psegs m -> bytes_at psegs m 0x10758 EJT.
Proof.
  intros m MI.
  pose proof (ro_cells_image psegs m 0x10758 EJT MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as [_ H].
  cbn [cells_bytes cbytes] in H. rewrite app_nil_r in H. exact H.
Qed.

Lemma byte_list_eq : forall l1 l2 : list byte, map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
  induction l1 as [|b1 l1 IH]; intros [|b2 l2] H; cbn in H; try discriminate; [reflexivity|].
  inversion H. f_equal; [apply bv_eq; assumption| apply IH; assumption].
Qed.

Lemma ejt_entry : forall c, 8 <= c <= 34 ->
  firstn 4 (skipn (Z.to_nat (Z.shiftl (c - 8) 2)) EJT) = le4 (Z_to_bv 64 (ejt_sel c)).
Proof.
  intros c Hc.
  assert (H : exists n, c = 8 + Z.of_nat n /\ (n < 27)%nat) by (exists (Z.to_nat (c - 8)); lia).
  (nelim H 3%nat; intros n -> Hn).
  do 27 (destruct n as [|n]; [apply byte_list_eq; vm_compute; reflexivity|]). lia.
Qed.

Lemma ejt_read : forall m c, mem_inv psegs m -> 8 <= c <= 34 ->
  ov_read_bytes psegs m (wa (Z.shiftl (c - 8) 2 + 0x10758)) 4 = Some (le4 (Z_to_bv 64 (ejt_sel c))).
Proof.
  intros m c MI Hc. rewrite Z.add_comm, <- ejt_entry by exact Hc.
  apply (bytes_at_read psegs m 0x10758 EJT (Z.shiftl (c - 8) 2) 4 (ejt_bytes m MI)).
  - rewrite Z.shiftl_mul_pow2 by lia. lia.
  - change (length EJT) with 108%nat. rewrite Z.shiftl_mul_pow2 by lia. lia.
Qed.

Lemma ejt_sel_default : forall c, c <> 8 -> c <> 9 -> c <> 10 -> c <> 12 -> c <> 13 -> c <> 34 -> ejt_sel c = 0x3f0c.
Proof.
  intros. unfold ejt_sel.
  repeat match goal with |- context [?x =? ?y] => destruct (Z.eqb_spec x y); [lia|] end. reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

Section Emit.
  Variables (S : Z) (str tail : list byte).
  Hypothesis NONUL : ~ In (wb 0) str.
  Notation full := (str ++ wb 0 :: tail).
  Notation L := (Z.of_nat (length str)).
  Notation E := (esc_count str).
  Notation ch i := (bv_unsigned (chb str tail i)).
  Notation pos i := (CJ_pstr_A.pos str i).

  (* [comment removed for export] *)
  Variables (m2 : word -> option byte) (B off len' lo : Z) (sp : word) (canary : word) (F0 : bvmap 5 word)
            (x3 x4 : word).
  Notation SPF := (bv_unsigned sp - 112).
  Notation OUT := (B + off).
  Definition WE : list (Z * Z) := [(lo, SPF); (OUT, OUT + (L + E + 3))].

  Hypothesis SPRU : F_printf_iface.sprintf_u04x_stmt.
  Hypothesis STR2 : bytes_at psegs m2 S full.
  Hypothesis DISJ : S + L + 1 + Z.of_nat (length tail) <= B \/ B + len' <= S.
  Hypothesis STRLO : S + L + 1 + Z.of_nat (length tail) <= alloc_ceiling.
  Hypothesis BR : 0 < B /\ B + len' <= alloc_ceiling /\ (B + len' <= 0x10000 \/ 0x55000 <= B).
  Hypothesis OFF : 0 <= off.
  Hypothesis ROOM : off + (L + E + 3) + 1 <= len'.
  Hypothesis LOF : alloc_ceiling <= lo /\ lo <= SPF - 5936.
  Hypothesis SPhi : bv_unsigned sp < 2^62.

  Definition EINV (mm : word -> option byte) (bsc : list byte) : Prop :=
    u8arr psegs mm B bsc /\ Z.of_nat (length bsc) = len' /\ munch WE m2 mm /\ wmono psegs m2 mm
    /\ mem_inv psegs mm /\ stk psegs mm lo SPF /\ F_pad.ssp_cells mm canary.
  Definition FAG (Fc : bvmap 5 word) : Prop := forall k : bv 5, bv_unsigned k <> 10 -> reg_get Fc k = reg_get F0 k.

  Lemma S_bound2 : 0 <= S /\ S + L + 1 + Z.of_nat (length tail) <= 2^64.
  Proof. pose proof (bytes_at_bound _ _ _ _ STR2) as X. rewrite length_app in X. cbn [length] in X. lia. Qed.

  Lemma STR_at : forall mm, munch WE m2 mm -> bytes_at psegs mm S full.
  Proof.
    intros mm MU. pose proof S_bound2. (nelimp BR 3%nat; intros _ B2 _). pose proof LOF as [L1 _]. try rewrite alloc_ceiling_eq in *.
    pose proof (esc_count_range str).
    eapply bytes_at_transport; [exact STR2| exact MU|]. unfold WE. rewrite length_app. cbn [disjoint_from length]. split; [lia|]. split; [lia| exact I].
  Qed.

  (* [comment removed for export] *)
  Notation HST pc x1 x5 x6 x7 s0v x10 x11 x12 x13 x14 x15 x16 x17 s2v x28 x29 x30 x31 Fc fcc mm :=
    (MS (mkR x1 (Z_to_bv 64 SPF) x3 x4 x5 x6 x7 (Z_to_bv 64 s0v) (Z_to_bv 64 0x102bf) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 s2v) (Z_to_bv 64 L) (Z_to_bv 64 E) (Z_to_bv 64 32) (Z_to_bv 64 92) (Z_to_bv 64 26) (Z_to_bv 64 114)
             (Z_to_bv 64 0x10758) (Z_to_bv 64 34) (Z_to_bv 64 OUT) x28 x29 x30 x31)
        Fc (Z_to_bv 64 pc) fcc None mm (seg_rom psegs)).

  Definition emit_done : machine_state -> Prop :=
    fun ms' => exists mm bsc Fc fcc x1 x5 x6 x7 s0v x10 x11 x12 x13 x14 x15 x16 x17 s2v x28 x29 x30 x31,
      ms' = HST 0x146cc x1 x5 x6 x7 s0v x10 x11 x12 x13 x14 x15 x16 x17 s2v x28 x29 x30 x31 Fc fcc mm
      /\ EINV mm bsc /\ frm0 fcc /\ FAG Fc.

  (* [comment removed for export] *)
  Definition HEADK (i : Z) : Prop :=
    forall mm bsc Fc fcc x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
      EINV mm bsc -> frm0 fcc -> FAG Fc ->
      evt psegs emit_done (HST 0x14618 x1 x5 x6 x7 (OUT + pos i) x10 (Z_to_bv 64 (ch i)) x12 x13 x14 x15 x16 x17 (S + i + 1) x28 x29 x30 x31 Fc fcc mm).

  Ltac pre :=
    pose proof S_bound2 as SB; (nelimp BR 3%nat; intros B1 B2 B3); pose proof LOF as [LO1 LO2];
    try rewrite alloc_ceiling_eq in *; pose proof (esc_count_range str) as ER.

  (* [comment removed for export] *)
  Lemma emit_tail : forall i, 0 <= i < L -> (i + 1 < L -> HEADK (i + 1)) ->
    forall mm bsc Fc fcc x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 s0v,
      EINV mm bsc -> frm0 fcc -> FAG Fc ->
      evt psegs emit_done (HST 0x14604 x1 x5 x6 x7 s0v (Z_to_bv 64 (OUT + pos (i + 1))) x11 x12 x13 x14 x15 x16 x17 (S + i + 1) x28 x29 x30 x31 Fc fcc mm).
  Proof.
    intros i Hi K. intros until s0v. intros INV FRM FA. pre.
    (nelimp INV 7%nat; intros ARR LEN MU WM MI ST SSP).
    pose proof (ch_read S str tail mm (i + 1) (STR_at mm MU) ltac:(lia)) as RD. replace (S + (i + 1)) with (S + i + 1) in RD by lia.
    destruct (ch_range str tail NONUL (i + 1) ltac:(lia)) as [CR CZ].
    zstep. zstep. rewrite (land255 (ch (i + 1))) by lia. zstep. zstep.
    zstep. if_cases Kz; zify_cond Kz.
    - (* [comment removed for export] *)
      apply evt_done. unfold emit_done. nexists 22%nat. split; [reflexivity|]. split; [exact INV|]. split; [exact FRM| exact FA].
    - replace (S + i + 2) with (S + (i + 1) + 1) by lia. specialize (K ltac:(lia)). unfold HEADK in K. eapply K; [exact INV| exact FRM| exact FA].
  Qed.

  (* [comment removed for export] *)
  Ltac ustore ea e b tac :=
    lazymatch goal with
    | ARR : u8arr psegs ?m B ?buf |- _ =>
        let SOK := fresh "SOK" in let ARR' := fresh "ARR" in
        destruct (u8_store' m B buf ea (off + e) b ARR) as [SOK ARR'];
        [ lia | rewrite ?upd_length; lia
        | clear ARR; step;
          lazymatch goal with
          | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m1 ?a ?bs) _) =>
              replace (write_to_mem m1 a bs) with (write_to_mem m1 (wa ea) [b])
                by (f_equal; first [tac| unfold wa; f_equal; lia]);
              store_done; rename ARR' into ARR
          end ]
    end.

  (* [comment removed for export] *)
  Lemma emit_sprintf_call : forall i, 0 <= i < L -> esc_extra (ch i) = 5 ->
    forall mm bsc Fc fcc x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31,
      EINV mm bsc -> frm0 fcc -> FAG Fc ->
      evt psegs (fun ms' => exists mm' bsc' Fc' fcc' x5' x6' x7' x11' x12' x13' x14' x15' x16' x17' x28' x29' x30' x31',
                   ms' = HST 0x1466c (Z_to_bv 64 0x1466c) x5' x6' x7' (OUT + pos i) (Z_to_bv 64 5) x11' x12' x13' x14' x15' x16' x17' (S + i + 1) x28' x29' x30' x31' Fc' fcc' mm'
                   /\ EINV mm' bsc' /\ frm0 fcc' /\ FAG Fc')
        (HST 0x17978 (Z_to_bv 64 0x1466c) x5 x6 x7 (OUT + pos i) (Z_to_bv 64 (OUT + pos i + 2)) (Z_to_bv 64 0x102bf) (Z_to_bv 64 (ch i)) x13 x14 x15 x16 x17 (S + i + 1) x28 x29 x30 x31 Fc fcc mm).
  Proof.
    intros i Hi EX5. intros until x31. intros INV FRM FA. pre.
    (nelimp INV 7%nat; intros ARR LEN MU WM MI ST SSP).
    destruct (ch_lt str tail NONUL i Hi) as [_ CR].
    pose proof (pos_bound str i ltac:(lia)) as PB1. pose proof (pos_next_bound str tail NONUL i Hi) as PB2.
    set (k := Z.to_nat (off + pos i + 2)).
    (nelim (u8arr_split3 mm B bsc k 6 ARR ltac:(lia)) 3%nat; intros A1 A2 A3).
    replace (B + Z.of_nat k) with (OUT + pos i + 2) in A2, A3 by lia.
    assert (SPE : bv_unsigned (Z_to_bv 64 SPF) = SPF) by (apply unsigned_lit; lia).
    eapply evt_cut.
    { eapply (SPRU (Z_to_bv 64 0x1466c) (Z_to_bv 64 SPF)) with (n := 6%nat) (lo := lo) (c := ch i); rewrite ?SPE, ?unsigned_lit by lia;
        unfold F_printf_iface.SPRINTF_DEPTH, F_printf_iface.GLOBALS_TOP;
        first [ exact A2 | reflexivity | exact ST | exact SSP | exact MI | exact FRM | lia | apply Z.mod_small; lia ]. }
    cbv beta. intros ms' PO.
    (nelim PO 26%nat; intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Ft fc' m' -> MUc WMc MI' FRM' FAc ST' OUTC SSP').
    rewrite SPE in MUc, ST'. rewrite ?unsigned_lit in MUc, OUTC by lia.
    replace (ret_pc (Z_to_bv 64 0x1466c)) with (Z_to_bv 64 0x1466c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply evt_done. nexists 18%nat. split; [reflexivity|].
    apply (u8arr_transport psegs _ mm m' _ _ A1) in MUc as A1'; [| exact WMc| cbn; rewrite firstn_length_le by lia; lia].
    apply (u8arr_transport psegs _ mm m' _ _ A3) in MUc as A3'; [| exact WMc| cbn; rewrite skipn_length; lia].
    replace (OUT + pos i + 2) with (B + (off + pos i + 2)) in OUTC, A3' by lia.
    destruct (u8arr_join3' m' B _ (off + pos i + 2) _ _ _ A1' ltac:(rewrite firstn_length_le by lia; lia) OUTC A3') as [ARR' L6].
    split; [| split; [exact FRM'|]].
    - split; [exact ARR'|]. split.
      { revert L6. generalize (F_fmt_fp_lib.zb (117 :: F_printf_iface.hex4_lower (ch i)) ++ Z_to_bv 8 0 :: skipn (Datatypes.S (length (117 :: F_printf_iface.hex4_lower (ch i)))) (firstn 6 (skipn k bsc))) as mid.
        intros mid L6. rewrite !length_app, L6, firstn_length_le, length_skipn by lia. lia. }
      split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MUc]. unfold WE, sub_fp. cbn. intros a [X [Y _]]. lia. }
      split; [eapply wmono_trans; [exact WM| exact WMc]|]. split; [exact MI'|]. split; [exact ST'| exact SSP'].
    - intros r Hr. rewrite (FAc r Hr). apply FA. exact Hr.
  Qed.

  (* [comment removed for export] *)
  Lemma emit_d0 : forall i, 0 <= i < L -> (i + 1 < L -> HEADK (i + 1)) -> esc_extra (ch i) = 1 ->
    forall mm bsc Fc fcc x1 x5 x6 x7 (v : Z) x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
      EINV mm bsc -> frm0 fcc -> FAG Fc -> 0 <= v < 256 ->
      evt psegs emit_done (HST 0x14600 x1 x5 x6 x7 (OUT + pos i) (Z_to_bv 64 (OUT + pos i + 2)) (Z_to_bv 64 v) x12 x13 x14 x15 x16 x17 (S + i + 1) x28 x29 x30 x31 Fc fcc mm).
  Proof.
    intros i Hi K EX1. intros until x31. intros INV FRM FA Hv. pre.
    (nelimp INV 7%nat; intros ARR LEN MU WM MI ST SSP).
    unfold F_pad.ssp_cells, F_pad.got_ssp, F_pad.ssp_guard in SSP. destruct SSP as [SSP1 SSP2].
    pose proof (pos_bound str i ltac:(lia)) as PB1. pose proof (pos_next_bound str tail NONUL i Hi) as PB2.
    unfold WE in MU.
    ustore (OUT + pos i + 2) (pos i + 2) (wb v) ltac:(symmetry; apply le1_lit8; lia).
    replace (OUT + pos i + 2) with (OUT + pos (i + 1)) by (rewrite (pos_step str tail NONUL i Hi); lia).
    eapply (emit_tail i Hi K); [| exact FRM| exact FA].
    split; [exact ARR|]. split; [rewrite upd_length; exact LEN|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    split; [exact SSP1| exact SSP2].
  Qed.

  (* [comment removed for export] *)
  Lemma emit_u : forall i, 0 <= i < L -> (i + 1 < L -> HEADK (i + 1)) -> esc_extra (ch i) = 5 ->
    forall mm bsc Fc fcc x1 x5 x6 x7 x11 x13 x14 x15 x16 x17 x28 x29 x30 x31,
      EINV mm bsc -> frm0 fcc -> FAG Fc ->
      evt psegs emit_done (HST 0x14664 x1 x5 x6 x7 (OUT + pos i) (Z_to_bv 64 (OUT + pos i + 2)) x11 (Z_to_bv 64 (ch i)) x13 x14 x15 x16 x17 (S + i + 1) x28 x29 x30 x31 Fc fcc mm).
  Proof.
    intros i Hi K EX5. intros until x31. intros INV FRM FA. pre.
    (nelimp INV 7%nat; intros ARR LEN MU WM MI ST SSP).
    pose proof (pos_bound str i ltac:(lia)) as PB1. pose proof (pos_next_bound str tail NONUL i Hi) as PB2.
    zstep. step.
    eapply evt_cut; [eapply (emit_sprintf_call i Hi EX5); [exact INV| exact FRM| exact FA]|].
    cbv beta. intros ms' PO.
    (nelim PO 22%nat; intros mm' bsc' Fc' fcc' x5' x6' x7' x11' x12' x13' x14' x15' x16' x17' x28' x29' x30' x31' -> INV' FRM' FA').
    clear ARR LEN MU WM MI ST SSP INV.
    (nelimp INV' 7%nat; intros ARR LEN MU WM MI ST SSP).
    zstep. zstep.
    replace (OUT + pos i + 6) with (OUT + pos (i + 1)) by (rewrite (pos_step str tail NONUL i Hi); lia).
    eapply (emit_tail i Hi K); [exact INV'| exact FRM'| exact FA'].
  Qed.

  Ltac dispatch := zstep; zstep; step; try rewrite sx32_lit by lia; zstep; step.

  Lemma emit_esc : forall i, 0 <= i < L -> (i + 1 < L -> HEADK (i + 1)) ->
    forall mm bsc Fc fcc x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
      EINV mm bsc -> frm0 fcc -> FAG Fc -> (ch i < 32 \/ ch i = 34 \/ ch i = 92) ->
      evt psegs emit_done (HST 0x14628 x1 x5 x6 x7 (OUT + pos i) (Z_to_bv 64 (ch i)) (Z_to_bv 64 (ch i)) x12 x13 x14 x15 x16 x17 (S + i + 1) x28 x29 x30 x31 Fc fcc mm).
  Proof using BR DISJ LOF NONUL OFF ROOM SPRU SPhi STR2 STRLO.
    intros i Hi K. intros until x31. intros INV FRM FA HC. pre.
    (nelimp INV 7%nat; intros ARR LEN MU WM MI ST SSP).
    unfold F_pad.ssp_cells, F_pad.got_ssp, F_pad.ssp_guard in SSP. destruct SSP as [SSP1 SSP2].
    destruct (ch_lt str tail NONUL i Hi) as [_ CR].
    pose proof (pos_bound str i ltac:(lia)) as PB1. pose proof (pos_next_bound str tail NONUL i Hi) as PB2.
    pose proof (esc_extra_range (ch i)) as EXR. pose proof (esc_extra_special (ch i) HC) as EX1.
    unfold WE in MU.
    ustore (OUT + pos i + 1) (pos i + 1) (wb 92) ltac:(reflexivity).
    pose proof (ch_read S str tail m i (STR_at m MU) ltac:(lia)) as RD.
    assert (INV1 : EINV m (upd bsc (Z.to_nat (off + (pos i + 1))) (wb 92))).
    { split; [exact ARR|]. split; [rewrite upd_length; exact LEN|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
      split; [exact SSP1| exact SSP2]. }
    (* [comment removed for export] *)
    assert (STJ : forall (pc : Z) (v : Z) x11 x12, esc_extra (ch i) = 1 -> 0 <= v < 256 ->
      (pc = 0x1465c /\ v = 92) \/ (pc = 0x1467c /\ v = 34) \/ (pc = 0x14694 /\ v = 114) ->
      evt psegs emit_done (HST pc x1 x5 x6 x7 (OUT + pos i) (Z_to_bv 64 (OUT + pos i + 2)) x11 x12 x13 x14 x15 x16 x17 (S + i + 1) x28 x29 x30 x31 Fc fcc m)).
    { intros pc v x11' x12' EXv Hv Hpc.
      destruct Hpc as [[-> Hv']|[[-> Hv']|[-> Hv']]];
        ustore (OUT + pos i + 2) (pos i + 2) (wb v) ltac:(rewrite Hv'; reflexivity); zstep;
        replace (OUT + pos i + 2) with (OUT + pos (i + 1)) by (rewrite (pos_step str tail NONUL i Hi); lia);
        (eapply (emit_tail i Hi K); [| exact FRM| exact FA]);
        (split; [exact ARR|]; split; [rewrite !upd_length; exact LEN|]; split; [exact MU|]; split; [exact WM|]; split; [exact MI|]; split; [exact ST|];
         split; [exact SSP1| exact SSP2]). }
    zstep. zstep. zstep. zstep. if_cases K4; zify_cond K4.
    - (* [comment removed for export] *)
      assert (HC2 : ch i < 8 \/ ch i = 92).
      { revert K4. destruct (Z_lt_le_dec (ch i) 8); [intros; lia|]. rewrite Z.mod_small by lia. intros; lia. }
      clear K4. zstep. if_cases K5; zify_cond K5.
      + (* [comment removed for export] *) eapply (emit_u i Hi K); [| exact INV1| exact FRM| exact FA].
        unfold esc_extra. replace (ch i <? 32) with true by (symmetry; apply Z.ltb_lt; lia).
        (* [comment removed for export] *) destruct (Z.eqb_spec (ch i) 34); [lia|]; destruct (Z.eqb_spec (ch i) 92); [lia|]; destruct (Z.eqb_spec (ch i) 8); [lia|]; destruct (Z.eqb_spec (ch i) 12); [lia|]; destruct (Z.eqb_spec (ch i) 10); [lia|]; destruct (Z.eqb_spec (ch i) 13); [lia|]; destruct (Z.eqb_spec (ch i) 9); [lia|]; cbn [orb]; lia.
      + (* [comment removed for export] *) eapply (STJ 0x1465c 92); [| lia| left; split; reflexivity]. rewrite K5. reflexivity.
    - (* [comment removed for export] *)
      assert (HCR : 8 <= ch i <= 34).
      { revert K4. destruct (Z_lt_le_dec (ch i) 8).
        - replace (ch i + -8) with ((ch i + -8 + 2^64) + (-1) * 2^64) by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. intros; lia.
        - rewrite Z.mod_small by lia. intros; lia. }
      clear K4.
      pose proof (ejt_read m (ch i) MI HCR) as RT.
      destruct (Z.eq_dec (ch i) 8) as [E8|N8]; [| destruct (Z.eq_dec (ch i) 9) as [E9|N9]; [| destruct (Z.eq_dec (ch i) 10) as [E10|N10];
        [| destruct (Z.eq_dec (ch i) 12) as [E12|N12]; [| destruct (Z.eq_dec (ch i) 13) as [E13|N13]; [| destruct (Z.eq_dec (ch i) 34) as [E34|N34]]]]]].
      + rewrite E8 in *. cbn [ejt_sel Z.eqb Pos.eqb] in RT. dispatch. zstep. zstep.
        eapply (emit_d0 i Hi K); [rewrite E8; reflexivity| exact INV1| exact FRM| exact FA| lia].
      + rewrite E9 in *. cbn [ejt_sel Z.eqb Pos.eqb] in RT. dispatch. zstep. zstep.
        eapply (emit_d0 i Hi K); [rewrite E9; reflexivity| exact INV1| exact FRM| exact FA| lia].
      + rewrite E10 in *. cbn [ejt_sel Z.eqb Pos.eqb] in RT. dispatch. zstep. zstep.
        eapply (emit_d0 i Hi K); [rewrite E10; reflexivity| exact INV1| exact FRM| exact FA| lia].
      + rewrite E12 in *. cbn [ejt_sel Z.eqb Pos.eqb] in RT. dispatch. zstep. zstep.
        eapply (emit_d0 i Hi K); [rewrite E12; reflexivity| exact INV1| exact FRM| exact FA| lia].
      + rewrite E13 in *. cbn [ejt_sel Z.eqb Pos.eqb] in RT. dispatch.
        eapply (STJ 0x14694 114); [reflexivity| lia| right; right; split; reflexivity].
      + rewrite E34 in *. cbn [ejt_sel Z.eqb Pos.eqb] in RT. dispatch.
        eapply (STJ 0x1467c 34); [reflexivity| lia| right; left; split; reflexivity].
      + (* [comment removed for export] *)
        rewrite (ejt_sel_default (ch i)) in RT by assumption.
        dispatch. eapply (emit_u i Hi K); [| exact INV1| exact FRM| exact FA].
        unfold esc_extra. replace (ch i <? 32) with true by (symmetry; apply Z.ltb_lt; lia).
        (* [comment removed for export] *) destruct (Z.eqb_spec (ch i) 34); [lia|]; destruct (Z.eqb_spec (ch i) 92); [lia|]; destruct (Z.eqb_spec (ch i) 8); [lia|]; destruct (Z.eqb_spec (ch i) 12); [lia|]; destruct (Z.eqb_spec (ch i) 10); [lia|]; destruct (Z.eqb_spec (ch i) 13); [lia|]; destruct (Z.eqb_spec (ch i) 9); [lia|]; cbn [orb]; lia.
  Qed.

  Lemma emit_head : forall i, 0 <= i < L -> (i + 1 < L -> HEADK (i + 1)) -> HEADK i.
  Proof.
    intros i Hi K. unfold HEADK. intros until x31. intros INV FRM FA. pre.
    (nelimp INV 7%nat; intros ARR LEN MU WM MI ST SSP).
    unfold F_pad.ssp_cells, F_pad.got_ssp, F_pad.ssp_guard in SSP. destruct SSP as [SSP1 SSP2].
    destruct (ch_lt str tail NONUL i Hi) as [_ CR].
    pose proof (pos_bound str i ltac:(lia)) as PB1. pose proof (pos_next_bound str tail NONUL i Hi) as PB2.
    pose proof (esc_extra_range (ch i)) as EXR.
    zstep. rewrite (land255 (ch i)) by lia.
    zstep. if_cases K1; zify_cond K1.
    { eapply (emit_esc i Hi K); [exact INV| exact FRM| exact FA| lia]. }
    zstep. if_cases K2; zify_cond K2.
    { eapply (emit_esc i Hi K); [exact INV| exact FRM| exact FA| lia]. }
    zstep. if_cases K3; zify_cond K3.
    2: { eapply (emit_esc i Hi K); [exact INV| exact FRM| exact FA| lia]. }
    (* [comment removed for export] *)
    assert (EX0 : esc_extra (ch i) = 0).
    { apply esc_extra_plain; lia. }
    zstep. unfold WE in MU.
    ustore (OUT + pos i + 1) (pos i + 1) (chb str tail i) ltac:(symmetry; apply le1_zxb).
    replace (OUT + pos i + 1) with (OUT + pos (i + 1)) by (rewrite (pos_step str tail NONUL i Hi); lia).
    eapply (emit_tail i Hi K); [| exact FRM| exact FA].
    split; [exact ARR|]. split; [rewrite upd_length; exact LEN|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    split; [exact SSP1| exact SSP2].
  Qed.

  Lemma emit_loop : forall (k : nat) (i : Z), Z.of_nat k = L - i -> 0 <= i < L -> HEADK i.
  Proof.
    induction k as [|k IH]; intros i Hk Hi; [lia|].
    apply emit_head; [exact Hi|]. intros Hn. apply IH; lia.
  Qed.
End Emit.


End CeilWrap.
(* [comment removed for export] *)
Ltac shh H := let T := type of H in idtac H ":" T.
Ltac shmem :=
  lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ ?m _) => idtac "PC" pc "MEM" m;
    repeat match goal with H : context [m] |- _ => shh H; revert H end end.
