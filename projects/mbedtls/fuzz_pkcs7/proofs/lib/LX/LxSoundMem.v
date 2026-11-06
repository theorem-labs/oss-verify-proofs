(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith PArith NArith List Bool Lia.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec MState Mem Cells Step Frame Exec CellsX Arr HeapIface.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtA AShadow.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxExpr LxDec LxMem LxStep LxRun LxDenot LxSoundExpr LxSoundDec.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section LXH.
Context {lxHT : lx_hints}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma reg_cases : forall r : bv 5,
  let k := bv_unsigned r in
  k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12
  \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24
  \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31.
Proof.
  intros r. pose proof (bv_unsigned_in_range 5 r) as R. unfold bv_modulus in R. cbn in R. cbn. lia.
Qed.

Definition rsget (rs : list sreg) (k : Z) : sreg :=
  if Z.eqb k 0 then RZ (ELit 0) else lget rs (Z.to_nat (k - 1)) (RZ (ELit 0)).

Lemma regs_den_get : forall E rs (r : bv 5),
  length rs = 31%nat ->
  reg_get (regs_den E rs) r = if Z.eqb (bv_unsigned r) 0 then w0 else rden E (rsget rs (bv_unsigned r)).
Proof.
  intros E rs r Hlen.
  do 31 (destruct rs as [|? rs]; [discriminate|]). destruct rs; [|discriminate].
  unfold reg_get, bvmap_get, bv_key.
  pose proof (reg_cases r) as C. cbn in C.
  repeat (destruct C as [C|C]; [rewrite C; reflexivity|]). rewrite C; reflexivity.
Qed.

Lemma regs_den_set : forall E rs (r : bv 5) v,
  length rs = 31%nat -> bv_unsigned r <> 0 ->
  bvmap_set r (rden E v) (regs_den E rs) = regs_den E (lset rs (Z.to_nat (bv_unsigned r - 1)) v).
Proof.
  intros E rs r v Hlen Hnz.
  do 31 (destruct rs as [|? rs]; [discriminate|]). destruct rs; [|discriminate].
  unfold bvmap_set, bv_key.
  pose proof (reg_cases r) as C. cbn in C.
  repeat (destruct C as [C|C]; [first [lia | rewrite C; reflexivity]|]). rewrite C; reflexivity.
Qed.

Lemma lset_length : forall {A} (l : list A) n x, length (lset l n x) = length l.
Proof. induction l; intros [|n] x; cbn; try reflexivity; rewrite IHl; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma cden_size : forall E c, csize (cden E c) = N.to_nat (cellx_size c).
Proof.
  intros E c; induction c as [i|w e|w k|w i|c IH o l|wr er]; cbn; try reflexivity.
  - destruct w as [|p]; [reflexivity|]. cbn.
    do 4 (destruct p as [p|p|]; try reflexivity).
  - destruct w as [|p]; [reflexivity|]. cbn.
    do 4 (destruct p as [p|p|]; try reflexivity).
Qed.

Lemma csden_size : forall E cs, cells_size (csden E cs) = N.to_nat (cells_sizeN cs).
Proof.
  intros E. unfold csden. induction cs as [|c cs IH]; cbn [map cells_size cells_sizeN]; [reflexivity|]. rewrite IH, cden_size. lia.
Qed.

Lemma cden_wf_XZ : forall E w e, cell_wf (cden E (XZ w e)).
Proof.
  intros E w e. destruct w as [|p]; [cbn; reflexivity|].
  cbn. do 4 (destruct p as [p|p|]; cbn; try exact I; try apply repeat_length).
Qed.

Lemma store_cell_wf : forall E w v, cell_wf (cden E (store_cell w v)).
Proof.
  intros E w v. unfold store_cell.
  destruct w as [|p]; [destruct v; apply cden_wf_XZ|].
  repeat match goal with |- context [match ?p with _ => _ end] => destruct p end; try apply cden_wf_XZ; exact I.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ld_val (w : N) (sx : bool) (bs : list byte) : word :=
  match w with
  | 8%N => bv_extract 0 64 (le_bytes_to_word bs)
  | 4%N => if sx then sext 64 (bv_extract 0 32 (le_bytes_to_word bs)) else zext 64 (bv_extract 0 32 (le_bytes_to_word bs))
  | 2%N => if sx then sext 64 (bv_extract 0 16 (le_bytes_to_word bs)) else zext 64 (bv_extract 0 16 (le_bytes_to_word bs))
  | 1%N => if sx then sext 64 (bv_extract 0 8 (le_bytes_to_word bs)) else zext 64 (bv_extract 0 8 (le_bytes_to_word bs))
  | _ => w0
  end.

Lemma mod_mod_pow2 : forall x k m, 0 <= k <= m -> (x mod 2 ^ m) mod 2 ^ k = x mod 2 ^ k.
Proof.
  intros x k m H. apply Z.mod_mod_divide.
  exists (2 ^ (m - k)). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

Lemma zswrap_mod_gen : forall k m x, 0 < k -> k <= m -> zswrap k (x mod 2 ^ m) = zswrap k x.
Proof.
  intros k m x Hk Hm. unfold zswrap. f_equal.
  rewrite <- (Z.add_mod_idemp_l x) by (apply Z.pow_nonzero; lia).
  rewrite <- (Z.add_mod_idemp_l (x mod 2 ^ m)) by (apply Z.pow_nonzero; lia).
  rewrite mod_mod_pow2 by lia. reflexivity.
Qed.

Lemma okw_cases : forall w, okw w = true -> w = 1%N \/ w = 2%N \/ w = 4%N \/ w = 8%N.
Proof.
  intros w H. destruct w as [|p]; [discriminate|].
  do 4 (try destruct p as [p|p|]; try discriminate); auto.
Qed.

(* [comment removed for export] *)
Lemma sxN_val : forall n z, 0 < n -> n <= 64 ->
  Z_to_bv 64 (bv_swrap (Z.to_N n) (bv_unsigned (Z_to_bv 64 z))) = Z_to_bv 64 (zswrap n z).
Proof.
  intros n z Hn Hle. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  rewrite Z2N.id by lia. cbn [Z.of_N].
  replace (2 ^ n `div` 2) with (2 ^ (n - 1)).
  2: { replace n with (Z.succ (n - 1)) at 2 by lia. rewrite Z.pow_succ_r by lia. rewrite Z.mul_comm, Z.div_mul by lia. reflexivity. }
  fold (zswrap n (z mod 2 ^ 64)). rewrite (zswrap_mod_gen n 64) by lia. reflexivity.
Qed.

Lemma zxN_val : forall n z, 0 <= n <= 64 ->
  Z_to_bv 64 (bv_unsigned (Z_to_bv 64 z) mod 2 ^ n) = Z_to_bv 64 (z mod 2 ^ n).
Proof.
  intros n z Hn. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N]. rewrite mod_mod_pow2 by lia. reflexivity.
Qed.

Lemma cell_value_sound : forall E O c sx r,
  osound E O ->
  cell_value O c sx = LReg r ->
  ld_val (cellx_size c) sx (cbytes (cden E c)) = rden E r.
Proof.
  intros E O c sx r HO H. destruct c as [i|w e|w k|w i|c o l|wr er]; cbn -[okw fresh_range esx elow Z.mul Z.of_N cden] in H; cbn [cellx_size].
  - injection H; intros <-. cbn. apply load_u64.
  - destruct w as [|p]; [discriminate|].
    do 4 (try destruct p as [p|p|]; try discriminate); injection H; intros <-; cbn [cellx_size cden cbytes ld_val rden Z.of_N Z.mul Pos.mul].
    + (* [comment removed for export] *) rewrite mkreg_den, zdenp_ok. apply load_u64.
    + (* [comment removed for export] *) rewrite !zdenp_ok. destruct sx.
      * rewrite sext_extract_le4. unfold sx32. rewrite esx_den, elow_den by (try exact HO; lia).
        rewrite (sxN_val 32) by lia. rewrite zswrap_mod_gen by lia. reflexivity.
      * rewrite zext_extract_le4. unfold zx32. rewrite elow_den by (try exact HO; lia). apply zxN_val. lia.
    + (* [comment removed for export] *) rewrite !zdenp_ok. destruct sx.
      * rewrite sext_extract_le2. unfold sx16. rewrite esx_den, elow_den by (try exact HO; lia).
        rewrite (sxN_val 16) by lia. rewrite zswrap_mod_gen by lia. reflexivity.
      * rewrite zext_extract_le2. unfold zx16. rewrite elow_den by (try exact HO; lia). apply zxN_val. lia.
    + (* [comment removed for export] *) rewrite !zdenp_ok. destruct sx.
      * rewrite sext_extract_byte. unfold sxb, bv_signed. rewrite esx_den, elow_den by (try exact HO; lia).
        rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N].
        change (2 ^ 8 `div` 2) with (2 ^ (8 - 1)). fold (zswrap 8 (zden E e mod 2 ^ 8)). change (8 * 1) with 8. rewrite !(zswrap_mod_gen 8 8) by lia. reflexivity.
      * rewrite zext_extract_byte. unfold zxb. rewrite elow_den by (try exact HO; lia). rewrite Z_to_bv_unsigned. reflexivity.
  - destruct (okw w); [|discriminate]. unfold fresh_range in H. destruct sx; discriminate.
  - (* [comment removed for export] *)
    destruct w as [|p]; [discriminate|].
    do 4 (try destruct p as [p|p|]; try discriminate); injection H; intros <-; cbn [cellx_size cden cbytes ld_val rden Z.of_N Z.mul Pos.mul];
      rewrite <- (w64_of_unsigned (ew E i)); change (bv_unsigned (ew E i)) with (zden E (EUv i)); rewrite !zdenp_ok.
    + (* [comment removed for export] *) destruct sx.
      * rewrite sext_extract_le4. unfold sx32. rewrite esx_den, elow_den by (try exact HO; lia).
        rewrite (sxN_val 32) by lia. rewrite zswrap_mod_gen by lia. reflexivity.
      * rewrite zext_extract_le4. unfold zx32. rewrite elow_den by (try exact HO; lia). apply zxN_val. lia.
    + (* [comment removed for export] *) destruct sx.
      * rewrite sext_extract_le2. unfold sx16. rewrite esx_den, elow_den by (try exact HO; lia).
        rewrite (sxN_val 16) by lia. rewrite zswrap_mod_gen by lia. reflexivity.
      * rewrite zext_extract_le2. unfold zx16. rewrite elow_den by (try exact HO; lia). apply zxN_val. lia.
  - (* [comment removed for export] *) destruct (okw l); [|discriminate]. unfold fresh_range in H. destruct sx; discriminate.
  - (* [comment removed for export] *) destruct (okw wr); [|discriminate]. unfold fresh_range in H. destruct sx; discriminate.
Qed.

Lemma Z_to_le_bytes_slice : forall n u o l, (o + l <= n)%nat ->
  firstn l (skipn o (Z_to_le_bytes n u)) = Z_to_le_bytes l (u / 2 ^ (8 * Z.of_nat o)).
Proof.
  intros n u o l H.
  replace n with (o + (l + (n - o - l)))%nat by lia.
  rewrite Z_to_le_bytes_app, skipn_app, length_Z_to_le_bytes, Nat.sub_diag, skipn_O.
  rewrite skipn_all2 by (rewrite length_Z_to_le_bytes; lia). cbn [app].
  rewrite Z_to_le_bytes_app, firstn_app, length_Z_to_le_bytes, Nat.sub_diag, firstn_O, app_nil_r.
  rewrite firstn_all2 by (rewrite length_Z_to_le_bytes; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma cden_lit_bytes : forall E n z, okw n = true ->
  cbytes (cden E (XZ n (ELit z))) = Z_to_le_bytes (N.to_nat n) (z mod 2 ^ 64).
Proof.
  intros E n z H. destruct (okw_cases n H) as [-> |[-> |[-> | ->]]]; lazy [cden zdenp cbytes N.to_nat Pos.to_nat Pos.iter_op Nat.add Z_to_le_bytes].
  - f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. cbn [bv_modulus Z.of_N].
    symmetry. apply mod_mod_pow2. lia.
  - unfold le2. rewrite Z_to_bv_unsigned. reflexivity.
  - unfold le4. rewrite Z_to_bv_unsigned. reflexivity.
  - unfold le8, word_to_le_bytes. rewrite Z_to_bv_unsigned. reflexivity.
Qed.

Lemma skipn_repeat : forall {A} (x : A) n o, skipn o (repeat x n) = repeat x (n - o).
Proof. intros A x n. induction n as [|n IH]; intros [|o]; cbn; try reflexivity. apply IH. Qed.
Lemma firstn_repeat : forall {A} (x : A) n l, (l <= n)%nat -> firstn l (repeat x n) = repeat x l.
Proof. intros A x n. induction n as [|n IH]; intros [|l] H; cbn; try reflexivity; [lia|]. rewrite IH by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma mk_slice2_ok : forall E b o l, (N.to_nat l <= length (cbytes (cden E b)) - N.to_nat o)%nat ->
  cellx_size (mk_slice2 b o l) = l /\ cell_wf (cden E (mk_slice2 b o l))
  /\ cbytes (cden E (mk_slice2 b o l)) = firstn (N.to_nat l) (skipn (N.to_nat o) (cbytes (cden E b))).
Proof.
  intros E b o l H.
  assert (GEN : cellx_size (XSl b o l) = l /\ cell_wf (cden E (XSl b o l))
                /\ cbytes (cden E (XSl b o l)) = firstn (N.to_nat l) (skipn (N.to_nat o) (cbytes (cden E b)))).
  { cbn [cellx_size cden cell_wf cbytes]. split; [reflexivity|]. split; [|reflexivity]. rewrite firstn_length, skipn_length. lia. }
  unfold mk_slice2. destruct b as [i|w e|w k|w i|c' o' l'|wr er]; try exact GEN.
  2:{ (* [comment removed for export] *)
      destruct (N.leb_spec (o + l) wr) as [LE|GT]; [|exact GEN].
      cbn [cellx_size cden cell_wf cbytes]. split; [reflexivity|]. split; [apply repeat_length|].
      cbn [cden cbytes] in H. rewrite skipn_repeat, firstn_repeat; [reflexivity|]. rewrite repeat_length in H. lia. }
  destruct e; try exact GEN. destruct (okw w) eqn:OW; [destruct (okw l) eqn:OL|]; cbn [andb]; try exact GEN.
  split; [reflexivity|]. split; [apply cden_wf_XZ|].
  rewrite (cden_lit_bytes E w) in H by assumption. rewrite length_Z_to_le_bytes in H.
  assert (L1 : (1 <= N.to_nat l)%nat) by (destruct (okw_cases l OL) as [-> |[-> |[-> | ->]]]; cbn; lia).
  rewrite !cden_lit_bytes by assumption. rewrite Z_to_le_bytes_slice by lia.
  unfold zslice. rewrite (Z.mod_small (_ mod 2 ^ (8 * Z.of_N l)) (2 ^ 64)).
  2:{ split; [apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia|].
      eapply Z.lt_le_trans; [apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia|]. apply Z.pow_le_mono_r; [lia|].
      destruct (okw_cases l OL) as [-> |[-> |[-> | ->]]]; cbn; lia. }
  rewrite <- (Z_to_le_bytes_mod (N.to_nat l) (z mod 2 ^ 64 / 2 ^ (8 * Z.of_nat (N.to_nat o)))).
  f_equal. rewrite !N_nat_Z. reflexivity.
Qed.

Lemma mk_slice_ok : forall E c o l, cell_wf (cden E c) -> (N.to_nat o + N.to_nat l <= N.to_nat (cellx_size c))%nat ->
  cellx_size (mk_slice c o l) = l /\ cell_wf (cden E (mk_slice c o l))
  /\ cbytes (cden E (mk_slice c o l)) = firstn (N.to_nat l) (skipn (N.to_nat o) (cbytes (cden E c))).
Proof.
  intros E c o l WF H. pose proof (cbytes_length _ WF) as LEN. rewrite cden_size in LEN.
  unfold mk_slice. destruct (N.eqb o 0 && N.eqb l (cellx_size c)) eqn:ID.
  - apply andb_prop in ID as [O0 LS]. apply N.eqb_eq in O0. apply N.eqb_eq in LS. subst o l.
    split; [reflexivity|]. split; [exact WF|]. change (N.to_nat 0) with 0%nat. rewrite skipn_O. rewrite firstn_all2 by lia. reflexivity.
  - clear ID. destruct c as [i|w e|w k|w i|c' o' l'|wr er]; try (apply mk_slice2_ok; lia).
    (* [comment removed for export] *)
    cbn [cellx_size] in H, LEN. cbn [cden cell_wf cbytes] in WF, LEN |- *.
    rewrite firstn_length, skipn_length in LEN.
    destruct (mk_slice2_ok E c' (o' + o) l ltac:(rewrite N2Nat.inj_add; lia)) as (M1 & M2 & M3).
    split; [exact M1|]. split; [exact M2|]. rewrite M3.
    rewrite skipn_firstn_comm, firstn_firstn, skipn_skipn. f_equal; [lia|]. f_equal. rewrite N2Nat.inj_add. lia.
Qed.

Lemma csden_wf_bytes_length : forall E cs, cells_wf (csden E cs) -> length (cells_bytes (csden E cs)) = N.to_nat (cells_sizeN cs).
Proof.
  intros E cs. unfold csden. induction cs as [|c cs IH]; intros WF; [reflexivity|]. cbn [map cells_wf cells_bytes cells_sizeN] in WF |- *.
  destruct WF as [W1 W2]. rewrite app_length, (IH W2), (cbytes_length _ W1), cden_size. lia.
Qed.

Lemma csden_wf_bytes_length0 : forall E cs, cells_wf (csden E cs) -> length (cells_bytes (csden E cs)) = cells_size (csden E cs).
Proof. intros E cs WF. rewrite (csden_wf_bytes_length E cs WF), csden_size. reflexivity. Qed.

(* [comment removed for export] *)
Lemma cell_lookup_sound : forall E cs off w c,
  0 <= off -> cell_lookup cs off w = Some c -> cells_wf (csden E cs) ->
  cellx_size c = w /\ cell_wf (cden E c)
  /\ cbytes (cden E c) = firstn (N.to_nat w) (skipn (Z.to_nat off) (cells_bytes (csden E cs)))
  /\ off + Z.of_N w <= Z.of_N (cells_sizeN cs).
Proof.
  intros E cs. unfold csden. induction cs as [|d cs IH]; intros off w c Hoff H WF; cbn -[mk_slice cellx_size] in H; [discriminate|].
  cbn [map cells_wf cells_bytes cells_sizeN] in WF |- *. destruct WF as [WD WCS].
  pose proof (cbytes_length _ WD) as LD. rewrite cden_size in LD.
  destruct (Z.ltb_spec off (Z.of_N (cellx_size d))).
  - destruct (Z.eqb off 0 && N.eqb (cellx_size d) w) eqn:EX.
    + apply andb_prop in EX as [E0 EW]. apply Z.eqb_eq in E0. apply N.eqb_eq in EW. subst off. injection H; intros <-.
      split; [exact EW|]. split; [exact WD|]. split; [|lia].
      change (Z.to_nat 0) with 0%nat. rewrite skipn_O, firstn_app, <- EW, <- LD, firstn_all, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
    + clear EX. destruct (Z.leb_spec (off + Z.of_N w) (Z.of_N (cellx_size d))); [|discriminate]. injection H; intros <-.
      destruct (mk_slice_ok E d (Z.to_N off) w WD ltac:(lia)) as (S1 & S2 & S3).
      split; [exact S1|]. split; [exact S2|]. split; [|lia].
      rewrite S3, skipn_app, firstn_app, skipn_length.
      replace (N.to_nat (Z.to_N off)) with (Z.to_nat off) by lia.
      replace (N.to_nat w - (length (cbytes (cden E d)) - Z.to_nat off))%nat with 0%nat by lia.
      rewrite firstn_O, app_nil_r. reflexivity.
  - destruct (IH (off - Z.of_N (cellx_size d)) w c ltac:(lia) H WCS) as (S1 & S2 & S3 & S4).
    split; [exact S1|]. split; [exact S2|]. split; [|lia].
    rewrite S3, skipn_app, LD. rewrite (skipn_all2 (cbytes _)) by lia. cbn [app]. f_equal. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma cut_cells_sound : forall E cs p lo hi bef aft,
  cut_cells cs p lo hi = (bef, aft) -> cells_wf (csden E cs) ->
  cells_wf (csden E bef) /\ cells_wf (csden E aft)
  /\ cells_bytes (csden E bef) = firstn (Z.to_nat (lo - p)) (cells_bytes (csden E cs))
  /\ cells_bytes (csden E aft) = skipn (Z.to_nat (hi - p)) (cells_bytes (csden E cs)).
Proof.
  intros E cs. unfold csden. induction cs as [|c cs IH]; intros p lo hi bef aft H WF; cbn -[mk_slice cellx_size] in H.
  - injection H; intros <- <-. cbn. rewrite firstn_nil, skipn_nil. repeat split; reflexivity.
  - cbn [map cells_wf cells_bytes cells_sizeN] in WF |- *. destruct WF as [WC WCS].
    pose proof (cbytes_length _ WC) as LC. rewrite cden_size in LC.
    remember (Z.of_N (cellx_size c)) as n eqn:Hn.
    destruct (cut_cells cs (p + n) lo hi) as [bef0 aft0] eqn:REC.
    destruct (IH _ _ _ _ _ REC WCS) as (B1 & A1 & B3 & A3).
    injection H; intros EA EB.
    split; [|split; [|split]].
    + subst bef. destruct (Z.ltb_spec p lo); [|exact B1]. destruct (Z.leb_spec (p + n) lo).
      * cbn [map cells_wf]. split; [exact WC| exact B1].
      * destruct (mk_slice_ok E c 0 (Z.to_N (lo - p)) WC ltac:(lia)) as (M1 & M2 & M3). cbn [map cells_wf]. split; [exact M2| exact B1].
    + subst aft. destruct (Z.ltb_spec hi (p + n)); [|exact A1]. destruct (Z.leb_spec hi p).
      * cbn [map cells_wf]. split; [exact WC| exact A1].
      * destruct (mk_slice_ok E c (Z.to_N (hi - p)) (Z.to_N (p + n - hi)) WC ltac:(lia)) as (M1 & M2 & M3). cbn [map cells_wf]. split; [exact M2| exact A1].
    + subst bef. rewrite firstn_app, LC. destruct (Z.ltb_spec p lo).
      * destruct (Z.leb_spec (p + n) lo).
        -- cbn [map cells_bytes]. rewrite B3. rewrite (firstn_all2 (cbytes (cden E c))) by lia. f_equal. f_equal. lia.
        -- destruct (mk_slice_ok E c 0 (Z.to_N (lo - p)) WC ltac:(lia)) as (M1 & M2 & M3). cbn [map cells_bytes].
           rewrite M3, B3. change (N.to_nat 0) with 0%nat. rewrite skipn_O.
           replace (Z.to_nat (lo - (p + n))) with 0%nat by lia. replace (Z.to_nat (lo - p) - N.to_nat (cellx_size c))%nat with 0%nat by lia.
           rewrite !firstn_O, !app_nil_r. f_equal. lia.
      * rewrite B3. replace (Z.to_nat (lo - (p + n))) with 0%nat by lia. replace (Z.to_nat (lo - p)) with 0%nat by lia. rewrite !firstn_O. reflexivity.
    + subst aft. rewrite skipn_app, LC. destruct (Z.ltb_spec hi (p + n)).
      * destruct (Z.leb_spec hi p).
        -- cbn [map cells_bytes]. rewrite A3. replace (Z.to_nat (hi - (p + n))) with 0%nat by lia. replace (Z.to_nat (hi - p)) with 0%nat by lia.
           replace (0 - N.to_nat (cellx_size c))%nat with 0%nat by lia. rewrite !skipn_O. reflexivity.
        -- destruct (mk_slice_ok E c (Z.to_N (hi - p)) (Z.to_N (p + n - hi)) WC ltac:(lia)) as (M1 & M2 & M3). cbn [map cells_bytes].
           rewrite M3, A3. replace (Z.to_nat (hi - (p + n))) with 0%nat by lia. replace (Z.to_nat (hi - p) - N.to_nat (cellx_size c))%nat with 0%nat by lia.
           rewrite !skipn_O. f_equal. replace (N.to_nat (Z.to_N (hi - p))) with (Z.to_nat (hi - p)) by lia.
           apply firstn_all2. rewrite skipn_length. lia.
      * rewrite A3. rewrite (skipn_all2 (cbytes _)) by lia. cbn [app]. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma cell_store_sound : forall E cs off c cs',
  cell_store cs off c = Some cs' -> cells_wf (csden E cs) -> cell_wf (cden E c) ->
  0 <= off /\ off + Z.of_N (cellx_size c) <= Z.of_N (cells_sizeN cs)
  /\ cells_wf (csden E cs')
  /\ cells_bytes (csden E cs') = firstn (Z.to_nat off) (cells_bytes (csden E cs)) ++ cbytes (cden E c)
                                 ++ skipn (Z.to_nat off + N.to_nat (cellx_size c)) (cells_bytes (csden E cs)).
Proof.
  intros E cs off c cs' H WF WC. unfold cell_store in H.
  destruct (Z.leb_spec 0 off); [|discriminate]. destruct (Z.leb_spec (off + Z.of_N (cellx_size c)) (Z.of_N (cells_sizeN cs))); [|discriminate]. cbn [andb] in H.
  destruct (cut_cells cs 0 off (off + Z.of_N (cellx_size c))) as [bef aft] eqn:CUT. injection H; intros <-.
  destruct (cut_cells_sound E cs 0 off _ bef aft CUT WF) as (W1 & W2 & BB & BA).
  split; [lia|]. split; [lia|]. unfold csden in *. rewrite map_app. cbn [map]. split.
  - rewrite cells_wf_app. cbn [cells_wf]. split; [exact W1| split; [exact WC| exact W2]].
  - rewrite cells_bytes_app. cbn [cells_bytes]. rewrite BB, BA. f_equal; [f_equal; lia|]. f_equal. f_equal. lia.
Qed.

Section LoadSound.
  Variable segs : list Segment.
  Variable L : asan_layout.
  Variable CS : Z -> Prop.
  Variable E : env.
  Variable m : mem.

  Definition fresh_ok (w : N) (sx : bool) (bs : list byte) (lo hi : Z) : Prop :=
    exists v, ld_val w sx bs = Z_to_bv 64 v /\ lo <= v <= hi.

  Definition lres_ok (a : expr) (w : N) (sx : bool) (r : lres) : Prop :=
    match r with
    | LReg rg => exists bs, ov_read_bytes segs m (Z_to_bv 64 (zden E a)) (N.to_nat w) = Some bs /\ ld_val w sx bs = rden E rg
    | LFresh lo hi => exists bs, ov_read_bytes segs m (Z_to_bv 64 (zden E a)) (N.to_nat w) = Some bs /\ fresh_ok w sx bs lo hi
    | LShb c oa on => w = 1%N /\ exists k : byte,
        ov_read_bytes segs m (Z_to_bv 64 (zden E a)) 1 = Some [k]
        /\ ld_val 1 sx [k] = Z_to_bv 64 (bv_unsigned k) /\ 0 <= bv_unsigned k <= 7
        /\ (forall n, 1 <= n -> zden E oa <= zden E c -> zden E c + n <= zden E oa + zden E on ->
              bv_unsigned k = 0 \/ (zden E c mod 8 + (n - 1) < bv_unsigned k /\ bv_unsigned k <= 7))
    | LNone => True
    end.

  Lemma Z_to_bv_signed64 : forall x : bv 64, Z_to_bv 64 (bv_signed x) = x.
  Proof.
    intros x. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
    cbn [Z.of_N]. pose proof (bv_unsigned_in_range 64 x) as R. unfold bv_modulus in R. cbn [Z.of_N] in R.
    set (u := bv_unsigned x) in *. set (M := 2 ^ 64) in *.
    pose proof (Z.div_mod (u + M `div` 2) M ltac:(subst M; lia)) as D.
    set (q := (u + M `div` 2) `div` M) in *.
    replace ((u + M `div` 2) `mod` M - M `div` 2) with (u - q * M) by lia.
    rewrite <- Z.add_opp_r, <- Z.mul_opp_l, Z.mod_add by (subst M; lia). apply Z.mod_small. lia.
  Qed.

  Lemma ld_val_fresh : forall w sx bs lo hi,
    okw w = true -> fresh_range w sx = LFresh lo hi -> fresh_ok w sx bs lo hi.
  Proof.
    intros w sx bs lo hi Hw H. unfold fresh_range in H.
    destruct (okw_cases w Hw) as [-> |[-> |[-> | ->]]]; destruct sx; injection H; intros <- <-; unfold fresh_ok, ld_val;
      cbn -[Z_to_bv bv_extract le_bytes_to_word sext zext Z.pow bv_unsigned bv_signed Z.opp Z.sub].
    all: try (rewrite sext_small; eexists; split; [reflexivity|];
              match goal with |- _ <= bv_signed ?x <= _ => pose proof (bv_signed_in_range _ x ltac:(discriminate)) as R end;
              unfold bv_half_modulus, bv_modulus in R; cbn in R; cbn; lia).
    all: try (rewrite zext_small; eexists; split; [reflexivity|];
              match goal with |- _ <= bv_unsigned ?x <= _ => pose proof (bv_unsigned_in_range _ x) as R end;
              unfold bv_modulus in R; cbn in R; cbn; lia).
    - exists (bv_signed (bv_extract 0 64 (le_bytes_to_word bs))). split; [symmetry; apply Z_to_bv_signed64|].
      match goal with |- _ <= bv_signed ?x <= _ => pose proof (bv_signed_in_range _ x ltac:(discriminate)) as R end.
      unfold bv_half_modulus, bv_modulus in R; cbn in R; cbn; lia.
    - exists (bv_unsigned (bv_extract 0 64 (le_bytes_to_word bs))). split; [symmetry; apply w64_of_unsigned|].
      match goal with |- _ <= bv_unsigned ?x <= _ => pose proof (bv_unsigned_in_range _ x) as R end.
      unfold bv_modulus in R; cbn in R; cbn; lia.
  Qed.

  Lemma read_at_chunk : forall (A : Z) cs (k : nat) c base,
    cells_at segs m A cs -> cell_at cs k = Some c ->
    base = A + Z.of_nat k ->
    ov_read_bytes segs m (Z_to_bv 64 base) (csize c) = Some (cbytes c).
  Proof. intros A cs k c base H Hk ->. apply (cells_at_read segs m A cs k c H Hk). Qed.

  Lemma cell_value_XZ_shape : forall O w e sx r, cell_value O (XZ w e) sx = r -> r = LNone \/ exists rg, r = LReg rg.
  Proof.
    intros O w e sx r H. cbn -[okw] in H. destruct w as [|p]; [| do 4 (try destruct p as [p|p|])];
      try (destruct (okw _)); subst; first [right; eexists; reflexivity | left; reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma terms_shr_den : forall O k ts ts', osound E O -> 0 < k -> terms_shr O k ts = Some ts' -> tden E ts = 2 ^ k * tden E ts'.
  Proof.
    intros O k ts. induction ts as [|[co a] ts IH]; intros ts' HO Hk H; cbn in H.
    - injection H; intros <-. cbn. lia.
    - destruct (terms_shr O k ts) as [r|] eqn:TS; [|discriminate].
      destruct (Z.eqb_spec (co mod 2 ^ k) 0).
      + injection H; intros <-. cbn. rewrite (IH r HO Hk eq_refl).
        pose proof (Z.div_mod co (2 ^ k) ltac:(lia)) as D. rewrite e, Z.add_0_r in D.
        rewrite D at 1. rewrite Z.mul_add_distr_l, Z.mul_assoc. reflexivity.
      + destruct (N.leb_spec (Z.to_N k) (eal O a)); [|discriminate]. injection H; intros <-. cbn [tden fst snd].
        rewrite (IH r HO Hk eq_refl). cbn [zden opden]. rewrite eatom_den. rewrite Z.shiftr_div_pow2 by lia.
        pose proof (eal_sound E O a HO) as D2.
        assert (DW : (2 ^ k | zden E a)).
        { eapply Z.divide_trans; [|exact D2]. exists (2 ^ (Z.of_N (eal O a) - k)).
          rewrite <- Z.pow_add_r by lia. f_equal. lia. }
        destruct DW as [q Hq]. rewrite Hq, Z.div_mul by lia. lia.
  Qed.

  Lemma sum_terms_den : forall ts c, zden E (sum_terms ts c) = tden E ts + zden E c.
  Proof. induction ts as [|[co a] ts IH]; intros c; cbn [sum_terms tden]; [lia|]. rewrite eadd_den, emulc_den, eatom_den, IH. lia. Qed.

  Lemma canon_atom_den : forall O a, osound E O -> zden E (canon_atom O a) = zden E a.
  Proof.
    intros O a HO. unfold canon_atom.
    destruct a as [z|i|i|x y|c x|o x y]; try apply eatom_den.
    destruct o; try apply eatom_den. destruct y as [k| | | | |]; try apply eatom_den.
    destruct (Z.ltb_spec 0 k) as [Hk|Hk]; [|apply eatom_den].
    destruct (lin_of x) as [ys c] eqn:LD. destruct ys as [|t ys']; [apply eatom_den|].
    destruct (terms_shr O k (t :: ys')) as [ts'|] eqn:TS; [|apply eatom_den].
    rewrite sum_terms_den. cbn [zden opden].
    pose proof (lin_of_den E x) as LL. rewrite LD in LL. cbn [fst snd] in LL.
    rewrite (terms_shr_den _ _ _ _ HO Hk TS) in LL. rewrite <- LL.
    rewrite !Z.shiftr_div_pow2 by lia. rewrite Z.mul_comm, Z.div_add_l by lia. reflexivity.
  Qed.

  Lemma canon_terms_den : forall O ts acc, osound E O -> zden E (canon_terms O ts acc) = tden E ts + zden E acc.
  Proof.
    intros O ts. induction ts as [|[co a] ts IH]; intros acc HO; cbn [canon_terms tden]; [lia|].
    rewrite (IH _ HO), eadd_den, emulc_den, (canon_atom_den _ _ HO). lia.
  Qed.

  Lemma shr_canon_den : forall O e, osound E O -> zden E (shr_canon O e) = zden E e.
  Proof.
    intros O e HO. unfold shr_canon. destruct (lin_of e) as [ts c] eqn:LD.
    rewrite (canon_terms_den _ _ _ HO). cbn [zden]. pose proof (lin_of_den E e) as LL. rewrite LD in LL. exact LL.
  Qed.

  Lemma ediff_litO_den : forall O a b off, osound E O -> ediff_litO O a b = Some off -> zden E a = zden E b + off.
  Proof.
    intros O a b off HO H. unfold ediff_litO in H.
    destruct (ediff_lit a b) as [z|] eqn:D1.
    - injection H; intros <-. exact (ediff_lit_den E a b z D1).
    - apply (ediff_lit_den E) in H. rewrite !(shr_canon_den _ _ HO) in H. exact H.
  Qed.

  Lemma load_chunks_sound : forall O mf a w sx r,
    osound E O -> Forall (mfact_ok segs L CS E m) mf ->
    load_chunks O mf a w sx = Some r -> lres_ok a w sx r.
  Proof.
    intros O mf a w sx r HO HM. induction mf as [|f mf IH]; intros H; [discriminate|].
    inversion HM as [|f' mf' Hf HM']; subst f' mf'. specialize (IH HM').
    cbn [load_chunks] in H.
    assert (CELLS : forall base cs, cells_at segs m (zdenp E base) (csden E cs) ->
              match ediff_litO O a base with
              | Some off =>
                  if (0 <=? off) && (off + Z.of_N w <=? Z.of_N (cells_sizeN cs))
                  then match cell_lookup cs off w with
                       | Some c => Some (cell_value O c sx)
                       | None => Some LNone
                       end
                  else load_chunks O mf a w sx
              | None => load_chunks O mf a w sx
              end = Some r -> lres_ok a w sx r).
    { intros base cs HC HH. destruct (ediff_litO O a base) as [off|] eqn:HD; [|exact (IH HH)].
      destruct (Z.leb_spec 0 off); [|exact (IH HH)].
      destruct (Z.leb_spec (off + Z.of_N w) (Z.of_N (cells_sizeN cs))); [|exact (IH HH)]. cbn [andb] in HH.
      destruct (cell_lookup cs off w) as [c|] eqn:HL; [|injection HH; intros <-; exact I].
      injection HH; intros <-.
      apply (ediff_litO_den O a base off HO) in HD.
      destruct HC as [WFC HB]. rewrite zdenp_ok in HB.
      destruct (cell_lookup_sound E cs off w c ltac:(lia) HL WFC) as (HW & WFc & BY & _).
      assert (RD : ov_read_bytes segs m (Z_to_bv 64 (zden E a)) (N.to_nat w) = Some (cbytes (cden E c))).
      { rewrite BY. replace (zden E a) with (zden E base + Z.of_nat (Z.to_nat off)) by lia.
        apply (bytes_at_ov_read segs m _ _ (Z.to_nat off) (N.to_nat w) HB).
        rewrite (csden_wf_bytes_length E cs WFC). lia. }
      assert (LENc : length (cbytes (cden E c)) = N.to_nat w) by (rewrite (cbytes_length _ WFc), cden_size, HW; reflexivity).
      destruct (cell_value O c sx) as [rg|lo hi|? ? ?|] eqn:HV; cbn [lres_ok]; [| | | exact I].
      - exists (cbytes (cden E c)). split; [exact RD|]. rewrite <- HW. eapply cell_value_sound; eauto.
      - exists (cbytes (cden E c)). split; [exact RD|].
        destruct c as [|w' e'|w' k'|w' i'|c' o' l'|wr' er']; [cbn in HV; discriminate| | | | |].
        + destruct (cell_value_XZ_shape _ _ _ _ _ HV) as [X|[rg X]]; discriminate.
        + cbn -[okw fresh_range] in HV. destruct (okw w') eqn:OK; [|discriminate]. cbn in HW. subst w'. eapply ld_val_fresh; eauto.
        + exfalso. cbn -[esx elow Z.mul Z.of_N] in HV. destruct w' as [|p]; [discriminate|]. do 4 (try destruct p as [p|p|]; try discriminate).
        + cbn -[okw fresh_range cden] in HV. destruct (okw l') eqn:OK; [|discriminate]. cbn in HW. subst l'. eapply ld_val_fresh; eauto.
        + cbn -[okw fresh_range cden] in HV. destruct (okw wr') eqn:OK; [|discriminate]. cbn in HW. subst wr'. eapply ld_val_fresh; eauto.
      - exfalso. destruct c as [|w' e'|w' k'|w' i'|c' o' l'|wr' er']; [cbn in HV; discriminate| | | | |].
        + destruct (cell_value_XZ_shape _ _ _ _ _ HV) as [X|[rg X]]; discriminate.
        + cbn -[okw fresh_range] in HV. destruct (okw w'); [unfold fresh_range in HV; destruct sx; discriminate| discriminate].
        + cbn -[esx elow Z.mul Z.of_N] in HV. destruct w' as [|p]; [discriminate|]. do 4 (try destruct p as [p|p|]; try discriminate).
        + cbn -[okw fresh_range cden] in HV. destruct (okw l'); [unfold fresh_range in HV; destruct sx; discriminate| discriminate].
        + cbn -[okw fresh_range cden] in HV. destruct (okw wr'); [unfold fresh_range in HV; destruct sx; discriminate| discriminate]. }
    destruct f as [base cs|base cs|b n k|lo hi|oa on|ok_k ok_l sh_l|ra_ rw_ rl_ rn_ rwr_|mW mi mj|mi mj|ml mX mi mj|ml ma mn|ml ma mn|qbl qok|ql qbl qsp qX qi qj|ql qs qa qn|qa qn qbl|ql qk|qj qo qn qxs qok]; try exact (IH H).
    - apply (CELLS base cs); [|exact H]. cbn in Hf. exact (proj1 Hf).
    - apply (CELLS base cs); [|exact H]. cbn in Hf. exact Hf.
  Qed.

  (* [comment removed for export] *)
  Lemma read_in_bytes : forall b bs (x : Z) (w : nat),
    bytes_at segs m b bs -> b <= x -> x + Z.of_nat w <= b + Z.of_nat (length bs) ->
    exists bs', ov_read_bytes segs m (Z_to_bv 64 x) w = Some bs' /\ length bs' = w.
  Proof.
    intros b bs x w HB H1 H2.
    pose proof (bytes_at_ov_read segs m b bs (Z.to_nat (x - b)) w HB ltac:(lia)) as R.
    replace (b + Z.of_nat (Z.to_nat (x - b))) with x in R by lia.
    eexists. split; [exact R|]. rewrite firstn_length, skipn_length. lia.
  Qed.

  Lemma read_in_stk : forall lo hi (x : Z) (w : nat),
    stk segs m lo hi -> lo <= x -> x + Z.of_nat w <= hi ->
    exists bs', ov_read_bytes segs m (Z_to_bv 64 x) w = Some bs' /\ length bs' = w.
  Proof.
    intros lo hi x w ST H1 H2.
    destruct (stk_bytes segs m lo hi ST ltac:(lia)) as (bs & Hlen & HB).
    eapply read_in_bytes; [exact HB| lia | rewrite Hlen; lia].
  Qed.

  Lemma find_shr3_den : forall ts x rest, find_shr3 ts = Some (x, rest) -> tden E ts = Z.shiftr (zden E x) 3 + tden E rest.
  Proof.
    induction ts as [|[k a] ts IH]; intros x rest H; cbn in H; [discriminate|].
    destruct k as [|p|p]; try (destruct (find_shr3 ts) as [[x' r']|] eqn:F; [|discriminate]; injection H; intros <- <-; cbn; rewrite (IH _ _ eq_refl); lia).
    destruct p; try (destruct (find_shr3 ts) as [[x' r']|] eqn:F; [|discriminate]; injection H; intros <- <-; cbn; rewrite (IH _ _ eq_refl); lia).
    destruct a as [| | | | |o u v]; try (destruct (find_shr3 ts) as [[x' r']|] eqn:F; [|discriminate]; injection H; intros <- <-; cbn -[Z.mul]; rewrite (IH _ _ eq_refl); lia).
    destruct o; try (destruct (find_shr3 ts) as [[x' r']|] eqn:F; [|discriminate]; injection H; intros <- <-; cbn -[Z.mul opden]; rewrite (IH _ _ eq_refl); lia).
    destruct v as [z| | | | |]; try (destruct (find_shr3 ts) as [[x' r']|] eqn:F; [|discriminate]; injection H; intros <- <-; cbn -[Z.mul opden]; rewrite (IH _ _ eq_refl); lia).
    destruct (Z.eq_dec z 3) as [->|NE].
    - injection H; intros <- <-. cbn -[Z.shiftr]. lia.
    - destruct z as [|q|q]; try (destruct (find_shr3 ts) as [[x' r']|] eqn:F; [|discriminate]; injection H; intros <- <-; cbn -[Z.mul opden]; rewrite (IH _ _ eq_refl); lia).
      do 2 (try destruct q as [q|q|]); try (destruct (find_shr3 ts) as [[x' r']|] eqn:F; [|discriminate]; injection H; intros <- <-; cbn -[Z.mul opden]; rewrite (IH _ _ eq_refl); lia).
      exfalso. apply NE. reflexivity.
  Qed.


  Lemma shadow_split_den : forall sb a x r,
    shadow_split sb a = Some (x, r) -> zden E a = zden E sb + Z.shiftr (zden E x) 3 + zden E r.
  Proof.
    intros sb a x r H. unfold shadow_split in H.
    destruct (lin_of a) as [ts ka] eqn:La.
    destruct (find_shr3 ts) as [[x' rest]|] eqn:F.
    - match type of H with (if ?c then _ else _) = _ => destruct c; [discriminate|] end. injection H; intros <- <-.
      pose proof (find_shr3_den _ _ _ F) as D.
      pose proof (lin_of_den E a) as LA. rewrite La in LA. cbn [fst snd] in LA.
      rewrite eadd_den, emulc_den, of_terms_den. lia.
    - destruct (is_lit (eadd a (emulc (-1) sb))) as [kk|] eqn:LK; [|discriminate]. injection H; intros <- <-.
      apply is_lit_den with (E := E) in LK. rewrite eadd_den, emulc_den in LK. cbn [zden].
      rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. rewrite Z.mul_comm, Z.div_mul by lia. lia.
  Qed.

  Lemma sh_c_den : forall x r, zden E (sh_c x r) = zden E x + 8 * zden E r.
  Proof. intros x r. unfold sh_c. rewrite eadd_den, emulc_den. reflexivity. Qed.

  Lemma shadow_addr : forall A, zdenp E (ac_sb A) = al_sb L -> forall a x r, shadow_split (ac_sb A) a = Some (x, r) ->
    zden E a = shadow_of L (zden E (sh_c x r)).
  Proof.
    intros A Hsb a x r H. apply shadow_split_den in H.
    unfold shadow_of. rewrite <- Hsb, zdenp_ok, sh_c_den. rewrite Z.shiftr_div_pow2 in H by lia.
    change (2 ^ 3) with 8 in H. replace (zden E x + 8 * zden E r) with (zden E x + zden E r * 8) by lia.
    rewrite Z.div_add by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Variable C : lxcfg.
  Hypothesis HACC : forall A, c_acc C = Some A -> zdenp E (ac_sb A) = al_sb L.

  Lemma ld_val_byte_small : forall sx (k : byte), bv_unsigned k <= 7 -> ld_val 1 sx [k] = Z_to_bv 64 (bv_unsigned k).
  Proof.
    intros sx k Hk. cbn -[sext zext bv_extract le_bytes_to_word Z_to_bv]. destruct sx.
    - rewrite sext_extract_byte. unfold sxb. f_equal. unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
      pose proof (bv_unsigned_in_range 8 k). cbn [Z.of_N]. cbn. rewrite Z.mod_small; lia.
    - rewrite zext_extract_byte. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma marr_cases : forall (w : N), w = 1%N \/ w = 4%N \/ w = 8%N \/ (w <> 1%N /\ w <> 4%N /\ w <> 8%N).
  Proof. intros w. destruct (N.eq_dec w 1); [tauto|]. destruct (N.eq_dec w 4); [tauto|]. destruct (N.eq_dec w 8); tauto. Qed.

  Lemma marr_bytes : forall mm a w l n wr, mfact_ok segs L CS E mm (MArr a w l n wr) ->
    exists bs, bytes_at segs mm (zden E a) bs /\ Z.of_nat (length bs) = Z.of_N w * zden E n
               /\ (wr = true -> wr_at segs mm (zden E a) (Z.of_N w * zden E n)).
  Proof.
    intros mm a w l n wr H.
    destruct (marr_cases w) as [-> |[-> |[-> | (N1 & N4 & N8)]]].
    - cbn -[u8arr bytes_at ldenb Z.of_nat Z.mul] in H. rewrite ?zdenp_ok in H.
      destruct H as [H HL]. exists (ldenb E l). destruct wr.
      + destruct H as [HB HW]. split; [exact HB|]. split; [lia|]. intros _. rewrite <- HL. 
        replace (Z.of_N 1 * Z.of_nat (length (ldenb E l))) with (Z.of_nat (length (ldenb E l))) by lia. exact HW.
      + split; [exact H|]. split; [lia|]. intros; discriminate.
    - cbn -[u32arr bytes_at ldenw u32s Z.of_nat Z.mul] in H. rewrite ?zdenp_ok in H.
      destruct H as [H HL]. exists (u32s (ldenw E l)). rewrite u32s_length. destruct wr.
      + destruct H as [HB HW]. split; [exact HB|]. split; [lia|]. intros _. rewrite <- HL.
        replace (Z.of_N 4 * Z.of_nat (length (ldenw E l))) with (4 * Z.of_nat (length (ldenw E l))) by lia. exact HW.
      + split; [exact H|]. split; [lia|]. intros; discriminate.
    - cbn -[u64arr bytes_at ldenw u64s Z.of_nat Z.mul] in H. rewrite ?zdenp_ok in H.
      destruct H as [H HL]. exists (u64s (ldenw E l)). rewrite u64s_length. destruct wr.
      + destruct H as [HB HW]. split; [exact HB|]. split; [lia|]. intros _. rewrite <- HL.
        replace (Z.of_N 8 * Z.of_nat (length (ldenw E l))) with (8 * Z.of_nat (length (ldenw E l))) by lia. exact HW.
      + split; [exact H|]. split; [lia|]. intros; discriminate.
    - exfalso. destruct w as [|p]; [exact H|]. repeat (destruct p as [p|p|]; try exact H; try congruence).
  Qed.

  Lemma load_other_sound : forall din pf O mf a w sx,
    (forall pf a n b k, Forall (pfact_ok CS E) pf -> din pf a n b k = true ->
       zden E b <= zden E a /\ zden E a + zden E n <= zden E b + zden E k) ->
    osound E O -> Forall (mfact_ok segs L CS E m) mf -> Forall (pfact_ok CS E) pf ->
    lres_ok a w sx (load_other din C pf O mf (mf) a w sx).
  Proof.
    intros din pf O mf0 a w sx dec_inside_sound HO HM HP.
    generalize mf0 at 2. intros all. revert HM.
    induction mf0 as [|f mf IH]; intros HM; [exact I|].
    inversion HM as [|f' mf' Hf HM']; subst f' mf'. specialize (IH HM').
    destruct f as [base cs|base cs|b n k|lo hi|oa on|ok_k ok_l sh_l|ra_ rw_ rl_ rn_ rwr_|mW mi mj|mi mj|ml mX mi mj|ml ma mn|ml ma mn|qbl qok|ql qbl qsp qX qi qj|ql qs qa qn|qa qn qbl|ql qk|qj qo qn qxs qok]; cbn [load_other]; try exact IH.
    - (* [comment removed for export] *) destruct (okw w) eqn:OK; [|exact IH]. destruct (din pf a (ELit (Z.of_N w)) b n) eqn:DI; [|exact IH].
      cbn [andb]. destruct Hf as [HB HL]. rewrite !zdenp_ok in HB, HL.
      apply (dec_inside_sound _ _ _ _ _ HP) in DI. cbn [zden] in DI.
      destruct (read_in_bytes _ _ (zden E a) (N.to_nat w) HB ltac:(lia) ltac:(lia)) as (bs' & RD & LEN).
      destruct (fresh_range w sx) as [|lo hi| |] eqn:FR; try (unfold fresh_range in FR; destruct sx; discriminate).
      cbn [lres_ok]. exists bs'. split; [exact RD|]. eapply ld_val_fresh; eauto.
    - (* [comment removed for export] *) destruct (okw w) eqn:OK; [|exact IH]. destruct (din pf a (ELit (Z.of_N w)) lo (esub hi lo)) eqn:DI; [|exact IH].
      cbn [andb]. cbn in Hf. rewrite !zdenp_ok in Hf.
      apply (dec_inside_sound _ _ _ _ _ HP) in DI. cbn [zden] in DI. rewrite esub_den in DI.
      destruct (read_in_stk _ _ (zden E a) (N.to_nat w) Hf ltac:(lia) ltac:(lia)) as (bs' & RD & LEN).
      destruct (fresh_range w sx) as [|lo' hi'| |] eqn:FR; try (unfold fresh_range in FR; destruct sx; discriminate).
      cbn [lres_ok]. exists bs'. split; [exact RD|]. eapply ld_val_fresh; eauto.
    - (* [comment removed for export] *) destruct (c_acc C) as [A|] eqn:HCA; [|exact IH]. destruct w as [|p]; [exact IH|]. destruct p as [p|p|]; try exact IH.
      destruct (shadow_split (ac_sb A) a) as [[x kr]|] eqn:SS; [|exact IH].
      pose proof (shadow_addr A (HACC A eq_refl) _ _ _ SS) as SA. set (c := sh_c x kr) in *.
      cbn in Hf. rewrite !zdenp_ok in Hf.
      destruct (N.leb_spec 3 (eal O c)) as [AL|AL]; cbn [andb].
      + destruct (din pf c (ELit 8) oa on) eqn:DI.
        * apply (dec_inside_sound _ _ _ _ _ HP) in DI. cbn [zden] in DI.
          pose proof (eal_mod E O c 3 HO AL) as M. change (2 ^ Z.of_N 3) with 8 in M.
          cbn [lres_ok]. exists [Z_to_bv 8 0]. split.
          -- eapply aobj_shadow0_al; eauto; lia.
          -- cbn -[sext zext bv_extract le_bytes_to_word Z_to_bv]. destruct sx; [rewrite sext_extract_byte|rewrite zext_extract_byte]; reflexivity.
        * destruct (din pf c (ELit 1) oa on) eqn:DI1; [|exact IH].
          apply (dec_inside_sound _ _ _ _ _ HP) in DI1. cbn [zden] in DI1.
          cbn [lres_ok]. split; [reflexivity|].
          destruct (aobj_shadow1_at segs L CS m _ _ (zden E c) (zden E a) Hf ltac:(lia) SA) as (kb & RD & VOK).
          exists kb. unfold shadow_val_ok in VOK. pose proof (bv_unsigned_in_range 8 kb) as KR.
          split; [exact RD|]. split; [apply ld_val_byte_small; lia|]. split; [lia|].
          intros n Hn H1 H2.
          destruct (aobj_shadowN_at segs L CS m _ _ (zden E c) n (zden E a) Hf H1 H2 Hn SA) as (kb' & RD' & VOK').
          rewrite RD in RD'. injection RD'; intros <-. unfold shadow_val_okN in VOK'. lia.
      + destruct (din pf c (ELit 1) oa on) eqn:DI1; [|exact IH].
        apply (dec_inside_sound _ _ _ _ _ HP) in DI1. cbn [zden] in DI1.
        cbn [lres_ok]. split; [reflexivity|].
        destruct (aobj_shadow1_at segs L CS m _ _ (zden E c) (zden E a) Hf ltac:(lia) SA) as (kb & RD & VOK).
        exists kb. unfold shadow_val_ok in VOK. pose proof (bv_unsigned_in_range 8 kb) as KR.
        split; [exact RD|]. split; [apply ld_val_byte_small; lia|]. split; [lia|].
        intros n Hn H1 H2.
        destruct (aobj_shadowN_at segs L CS m _ _ (zden E c) n (zden E a) Hf H1 H2 Hn SA) as (kb' & RD' & VOK').
        rewrite RD in RD'. injection RD'; intros <-. unfold shadow_val_okN in VOK'. lia.
    - (* [comment removed for export] *)
      destruct (okw w) eqn:OK; [|exact IH].
      destruct (din pf a (ELit (Z.of_N w)) ra_ (emulc (Z.of_N rw_) rn_)) eqn:DI; [|exact IH]. cbn [andb].
      apply (dec_inside_sound _ _ _ _ _ HP) in DI. cbn [zden] in DI. rewrite emulc_den in DI.
      destruct (marr_bytes _ _ _ _ _ _ Hf) as (bs0 & HB & HL & _).
      destruct (read_in_bytes _ _ (zden E a) (N.to_nat w) HB ltac:(lia) ltac:(lia)) as (bs' & RD & LEN).
      destruct (fresh_range w sx) as [|lo hi| |] eqn:FR; try (unfold fresh_range in FR; destruct sx; discriminate).
      cbn [lres_ok]. exists bs'. split; [exact RD|]. eapply ld_val_fresh; eauto.
  Qed.
  (* [comment removed for export] *)
  Theorem sym_load_sound : forall ss a w sx,
    Forall (mfact_ok segs L CS E m) (s_mf ss) -> Forall (pfact_ok CS E) (s_pf ss) ->
    lres_ok a w sx (sym_load C ss a w sx).
  Proof.
    intros ss a w sx HM HP. unfold sym_load.
    pose proof (mk_oracle_sound CS E _ HP) as HO.
    destruct (load_chunks (oracle_of ss) (s_mf ss) a w sx) as [r|] eqn:HL.
    - eapply load_chunks_sound; eauto.
    - pose proof (load_other_sound dec_inside1 (s_pf ss) (oracle_of ss) (s_mf ss) a w sx (dec_inside1_sound CS E) HO HM HP) as L1.
      pose proof (load_other_sound dec_insideX (s_pf ss) (oracle_of ss) (s_mf ss) a w sx (dec_insideX_sound CS E) HO HM HP) as L2.
      destruct (load_other dec_inside1 C (s_pf ss) (oracle_of ss) (s_mf ss) (s_mf ss) a w sx); first [exact L2 | exact L1].
  Qed.
End LoadSound.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma Z_to_le_bytes_8_4 : forall z, Z_to_le_bytes 8 z = Z_to_le_bytes 4 z ++ Z_to_le_bytes 4 (Z.shiftr z 32).
Proof.
  intros z. cbn [Z_to_le_bytes app]. rewrite !Z.shiftr_shiftr by lia. cbn [Z.add Pos.add Pos.succ]. reflexivity.
Qed.
Lemma le8_le4 : forall v : word, le8 v = le4 v ++ le4 (Z_to_bv 64 (Z.shiftr (bv_unsigned v) 32)).
Proof.
  intros v. unfold le8, word_to_le_bytes, le4. rewrite Z_to_le_bytes_8_4. f_equal. f_equal.
  rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small.
  pose proof (bv_unsigned_in_range 64 v) as R. unfold bv_modulus in *.
  rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|].
  apply Z.div_lt_upper_bound; [lia|]. cbn in R |- *. lia.
Qed.
Lemma upd_app_mid : forall {X} (pre : list X) x post v, upd (pre ++ x :: post) (length pre) v = pre ++ v :: post.
Proof. induction pre as [|y pre IH]; intros x post v; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.
Lemma u32arr_write2 : forall segs m A ws (i : Z) (v : word),
  u32arr segs m A ws -> 0 <= i -> i + 2 <= Z.of_nat (length ws) ->
  u32arr segs (write_to_mem m (wa (A + 4 * i)) (le8 v)) A
         (upd (upd ws (Z.to_nat i) v) (Z.to_nat (i + 1)) (Z_to_bv 64 (Z.shiftr (bv_unsigned v) 32))).
Proof.
  intros segs m A ws i v [Hb Hw] Hi Hi2.
  set (v' := Z_to_bv 64 (Z.shiftr (bv_unsigned v) 32)).
  destruct (upd_app_split ws (Z.to_nat i) v ltac:(lia)) as (pre & y & post & E & Hlen & Hupd).
  destruct post as [|y2 post]. { exfalso. subst ws. rewrite app_length in Hi2. cbn in Hi2. lia. }
  assert (Hupd2 : upd (upd ws (Z.to_nat i) v) (Z.to_nat (i + 1)) v' = pre ++ v :: v' :: post).
  { rewrite Hupd. replace (pre ++ v :: y2 :: post) with ((pre ++ [v]) ++ y2 :: post) by (rewrite <- app_assoc; reflexivity).
    replace (Z.to_nat (i + 1)) with (length (pre ++ [v])) by (rewrite app_length; cbn; lia).
    rewrite upd_app_mid, <- app_assoc. reflexivity. }
  split.
  - eapply bytes_at_ext.
    { apply (bytes_at_write_inside segs m A (u32s ws) (4 * i) (le8 v) Hb); [lia|]. rewrite length_le8, u32s_length. lia. }
    rewrite Hupd2, E, !u32s_app. cbn [u32s]. rewrite le8_le4.
    replace (Z.to_nat (4 * i)) with (length (u32s pre)) by (rewrite u32s_length; lia).
    rewrite (app_assoc (le4 y)). rewrite (app_assoc (le4 v)).
    apply upd_bytes_mid. rewrite !app_length, !length_le4. reflexivity.
  - rewrite !upd_length. apply wr_at_write. exact Hw.
Qed.

Section StoreSound.
  Variable segs : list Segment.
  Variable L : asan_layout.
  Variable CS : Z -> Prop.
  Variable E : env.
  Variable m : mem.
  Variable C : lxcfg.
  (* [comment removed for export] *)
  Hypothesis HACC : forall A, c_acc C = Some A -> ac_got A = al_got L /\ ac_gsb A = al_gsb L /\ cs_ok L CS.
  Hypothesis HSB : forall A, c_acc C = Some A -> zdenp E (ac_sb A) = al_sb L.
  Hypothesis HPF : hp_frame segs (ehp E) (ecw E).   (* [comment removed for export] *)
  Hypothesis HBK : hp_blk (ecw E).                   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma bklist_eqb_eq : forall x y, bklist_eqb x y = true -> x = y.
  Proof.
    induction x as [|a n x IH|k]; intros [|a' n' y|k'] H; cbn in H; try discriminate; try reflexivity.
    - apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
      apply expr_eqb_eq in H1. apply expr_eqb_eq in H2. apply IH in H3. subst. reflexivity.
    - apply Nat.eqb_eq in H. subst. reflexivity.
  Qed.
  Lemma bl_suffix_incl : forall s bl b, bl_suffix s bl = true -> In b (blden E s) -> In b (blden E bl).
  Proof.
    intros s bl. induction bl as [|a n bl IH|k]; intros b H Hb; cbn [bl_suffix] in H.
    - destruct (bklist_eqb s BL0) eqn:Q; [apply bklist_eqb_eq in Q; subst s; exact Hb| discriminate].
    - destruct (bklist_eqb s (BCons a n bl)) eqn:Q; [apply bklist_eqb_eq in Q; subst s; exact Hb|].
      cbn. right. apply IH; [exact H| exact Hb].
    - destruct (bklist_eqb s (BLV k)) eqn:Q; [apply bklist_eqb_eq in Q; subst s; exact Hb| discriminate].
  Qed.
  Lemma ivs_cover_sound : forall pf b n ok, Forall (pfact_ok CS E) pf -> ivs_cover pf b n ok = true ->
    exists lo hi, In (lo, hi) (wden E ok) /\ lo <= zden E b /\ zden E b + zden E n <= hi.
  Proof.
    intros pf b n ok HP H.
    assert (OKC : forall test, (forall a' n' b' k', test a' n' b' k' = true -> zden E b' <= zden E a' /\ zden E a' + zden E n' <= zden E b' + zden E k') ->
                  opq_in test b n ok = true -> exists lo hi, In (lo, hi) (wden E ok) /\ lo <= zden E b /\ zden E b + zden E n <= hi).
    { intros test HT HO. unfold opq_in in HO. apply any_iv_exists in HO as (lo & hi & Hin & D). apply HT in D.
      rewrite eadd_den, emulc_den in D.
      exists (zdenp E lo), (zdenp E hi). split; [|rewrite !zdenp_ok; lia].
      unfold wden. apply in_map_iff. exists (lo, hi). split; [reflexivity| exact Hin]. }
    unfold ivs_cover in H.
    destruct (opq_in (fun a' n' b' k' => iv_inside_syn a' n' b' k') b n ok) eqn:E0.
    { eapply OKC; [|exact E0]. intros a' n' b' k' T. exact (iv_inside_syn_sound E _ _ _ _ T). }
    destruct (opq_in (dec_inside0 pf) b n ok) eqn:E1.
    { eapply OKC; [|exact E1]. intros a' n' b' k' T. exact (dec_inside0_sound CS E _ _ _ _ _ HP T). }
    eapply OKC; [|exact H]. intros a' n' b' k' T. exact (dec_inside_sound CS E _ _ _ _ _ HP T).
  Qed.
  Lemma apart_covers_sound : forall pf mf s b n x, Forall (pfact_ok CS E) pf -> Forall (mfact_ok segs L CS E m) mf ->
    apart_covers pf mf s b n = true -> zden E b <= x < zden E b + zden E n -> ~ in_block (blden E s) x.
  Proof.
    intros pf mf s b n x HP HM. induction mf as [|f mf IH]; intros H Hx; cbn [apart_covers] in H; [discriminate|].
    inversion HM as [|f' mf' Hf HM']; subst f' mf'.
    assert (REST : apart_covers pf mf s b n = true -> ~ in_block (blden E s) x) by (intros X; exact (IH HM' X Hx)).
    destruct f as [| | | | | | | | | | | | | | |qa qk qbl| |]; try exact (REST H).
    destruct (bl_suffix s qbl) eqn:SUF; [|exact (REST H)].
    assert (INB : (if iv_inside_syn b n qa qk then true else dec_inside pf b n qa qk) = true ->
                  zden E qa <= zden E b /\ zden E b + zden E n <= zden E qa + zden E qk).
    { intros Y. destruct (iv_inside_syn b n qa qk) eqn:SY; [exact (iv_inside_syn_sound E _ _ _ _ SY)| exact (dec_inside_sound CS E _ _ _ _ _ HP Y)]. }
    match type of H with (if ?c then _ else _) = true => destruct c eqn:Y end; [|exact (REST H)].
    specialize (INB eq_refl). intros (bk & Hin & Hbk). cbn [mfact_ok] in Hf. rewrite !zdenp_ok in Hf.
    destruct bk as [b0 k0]. cbn [fst snd] in Hbk.
    pose proof (Hf b0 k0 (bl_suffix_incl s qbl _ SUF Hin)). lia.
  Qed.
  Lemma bl_covers_sound : forall pf bl b n, Forall (pfact_ok CS E) pf -> bl_covers pf bl b n = true ->
    exists a k, In (zden E a, zden E k) (blden E bl) /\ zden E a <= zden E b /\ zden E b + zden E n <= zden E a + zden E k.
  Proof.
    intros pf bl b n HP. induction bl as [|a k bl IH|kv]; cbn -[iv_inside_syn dec_inside zdenp]; intros H; [discriminate| |discriminate].
    rewrite !zdenp_ok.
    destruct (iv_inside_syn b n a k) eqn:SY.
    { exists a, k. split; [left; reflexivity| exact (iv_inside_syn_sound E b n a k SY)]. }
    destruct (dec_inside pf b n a k) eqn:DI.
    { exists a, k. split; [left; reflexivity| exact (dec_inside_sound CS E pf b n a k HP DI)]. }
    destruct (IH H) as (a' & k' & Hin & X). exists a', k'. split; [right; exact Hin| exact X].
  Qed.

  (* [comment removed for export] *)
  Definition st_bytes (w : N) (rv : word) : list byte :=
    match w with 8%N => le8 rv | 4%N => le4 rv | 2%N => le2 rv | 1%N => le1 rv | _ => [] end.

  Lemma le1_lit : forall z, le1 (Z_to_bv 64 z) = [Z_to_bv 8 z].
  Proof.
    intros z. unfold le1. cbn. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned.
    unfold bv_wrap, bv_modulus. cbn [Z.of_N]. apply mod_mod_pow2. lia.
  Qed.

  Lemma store_cell_bytes : forall w v, okw w = true ->
    cbytes (cden E (store_cell w v)) = st_bytes w (rden E v).
  Proof.
    intros w v Hw.
    assert (X : forall i, Z_to_bv 64 (zden E (eatom (EUv i))) = ew E i).
    { intros i. cbn. rewrite Z.mul_1_l, Z.add_0_r. apply w64_of_unsigned. }
    destruct (okw_cases w Hw) as [-> |[-> |[-> | ->]]]; destruct v as [i|e]; cbn -[le8 le4 le2 le1 Z_to_bv zdenp Z.mul Z.add zden eatom];
      rewrite ?zdenp_ok; rewrite ?X, <- ?le1_lit, ?X; reflexivity.
  Qed.

  Lemma store_cell_size : forall w v, cellx_size (store_cell w v) = w.
  Proof.
    intros w v. unfold store_cell. destruct w as [|p]; [destruct v; reflexivity|].
    repeat match goal with |- context [match ?p with _ => _ end] => destruct p end; reflexivity.
  Qed.

  Lemma st_bytes_length : forall w rv, okw w = true -> length (st_bytes w rv) = N.to_nat w.
  Proof.
    intros w rv Hw. destruct (okw_cases w Hw) as [-> |[-> |[-> | ->]]]; cbn -[le8 le4 le2 le1];
      first [apply length_le1 | apply length_le2 | apply length_le4 | apply length_le8].
  Qed.

  (* [comment removed for export] *)
  Definition acls_ok (cl : acls) (a : Z) (w : Z) : Prop :=
    match cl with
    | AcClient => crange CS a w
    | AcShadow => forall j, 0 <= j < w -> exists c, CS c /\ a + j = shadow_of L c
    | AcImg => al_img_lo L <= a /\ a + w <= al_img_hi L
    end.

  Lemma in_some_crange_sound : forall pf crs a n,
    Forall (pfact_ok CS E) pf ->
    Forall (fun an => crange CS (zden E (fst an)) (zden E (snd an))) crs ->
    in_some_crange pf crs a n = true -> crange CS (zden E a) (zden E n).
  Proof.
    intros pf crs a n HP HC H. unfold in_some_crange in H.
    assert (H' : exists b k, In (b, k) crs /\ (zden E b <= zden E a /\ zden E a + zden E n <= zden E b + zden E k)).
    { destruct (any_iv (fun b k => iv_inside_syn a n b k) crs) eqn:D0.
      { apply any_iv_exists in D0 as (b & k & Hin & Hd). exists b, k. split; [exact Hin|]. exact (iv_inside_syn_sound E _ _ _ _ Hd). }
      destruct (any_iv (fun b k => dec_inside0 pf a n b k) crs) eqn:D2.
      { apply any_iv_exists in D2 as (b & k & Hin & Hd). exists b, k. split; [exact Hin|]. exact (dec_inside0_sound CS E _ _ _ _ _ HP Hd). }
      destruct (any_iv (fun b k => dec_inside1 pf a n b k) crs) eqn:D1.
      - apply any_iv_exists in D1 as (b & k & Hin & Hd). exists b, k. split; [exact Hin|]. exact (dec_inside1_sound CS E _ _ _ _ _ HP Hd).
      - apply any_iv_exists in H as (b & k & Hin & Hd). exists b, k. split; [exact Hin|]. exact (dec_insideX_sound CS E _ _ _ _ _ HP Hd). }
    destruct H' as (b & k & Hin & Hd).
    rewrite List.Forall_forall in HC. specialize (HC _ Hin). cbn in HC.
    intros x Hx. apply HC. lia.
  Qed.

  Lemma cranges_sound : forall pf mf,
    Forall (pfact_ok CS E) pf -> Forall (mfact_ok segs L CS E m) mf ->
    Forall (fun an => crange CS (zden E (fst an)) (zden E (snd an))) (cranges pf mf).
  Proof.
    intros pf mf HP HM. induction pf as [|f pf IH].
    - cbn. induction mf as [|g mf IHm]; [constructor|]. inversion HM; subst.
      destruct g; cbn; try (apply IHm; assumption). constructor; [|apply IHm; assumption].
      cbn. cbn in H1. rewrite !zdenp_ok in H1. exact (proj1 H1).
    - inversion HP; subst. destruct f; cbn; try (apply IH; assumption). constructor; [|apply IH; assumption].
      cbn. cbn in H1. rewrite !zdenp_ok in H1. exact H1.
  Qed.

  (* [comment removed for export] *)
  Lemma static_apart : forall cl a w S, cs_ok L CS ->
    (cl = AcClient \/ cl = AcShadow) -> acls_ok cl a w ->
    (S = al_got L \/ S = al_gsb L) -> 0 < w ->
    S + 8 <= a \/ a + w <= S.
  Proof.
    intros cl a w S CSOK Hcl H HS Hw.
    destruct (Z_lt_le_dec a (S + 8)); [|left; lia]. destruct (Z_lt_le_dec S (a + w)); [|right; lia]. exfalso.
    destruct CSOK as (C1 & C2 & C3 & _).
    (* [comment removed for export] *)
    set (x := Z.max a S).
    assert (Hxa : a <= x < a + w) by lia. assert (HxS : 0 <= x - S < 8) by lia.
    destruct Hcl as [-> | ->]; cbn in H.
    - specialize (H x Hxa). destruct (C2 (x - S) HxS) as [N1 N2].
      destruct HS as [-> | ->]; [apply N1|apply N2]; replace (_ + (x - _)) with x by lia; exact H.
    - destruct (H (x - a) ltac:(lia)) as (c & Hc & Hx). destruct (C3 c (x - S) Hc HxS) as [N1 N2].
      destruct HS as [-> | ->]; [apply N1|apply N2]; lia.
  Qed.

  Lemma stk_wr_at : forall mm lo hi a n, stk segs mm lo hi -> lo <= a -> a + n <= hi -> 0 <= n -> wr_at segs mm a n.
  Proof.
    intros mm lo hi a n (H1 & H2 & H) Ha Hn Hn0. split; [lia|]. split; [lia|].
    intros i Hi. apply (proj1 (H (a + i) ltac:(lia))).
  Qed.

  Lemma wr_at_write : forall mm a n b bs, wr_at segs mm a n -> wr_at segs (write_to_mem mm b bs) a n.
  Proof.
    intros mm a n b bs (H1 & H2 & H). split; [lia|]. split; [lia|]. intros i Hi. apply wview_write_mono. apply H. lia.
  Qed.

  Lemma bytes_at_nil_any : forall mm b, 0 <= b -> b <= 2 ^ 64 -> bytes_at segs mm b [].
  Proof. intros mm b H1 H2. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma marr_frame : forall mm a w l n wr (x : Z) xs,
    mfact_ok segs L CS E mm (MArr a w l n wr) ->
    0 <= x -> x + Z.of_nat (length xs) <= 2 ^ 64 ->
    (zden E n <= 0 \/ zden E a + Z.of_N w * zden E n <= x \/ x + Z.of_nat (length xs) <= zden E a) ->
    mfact_ok segs L CS E (write_to_mem mm (wa x) xs) (MArr a w l n wr).
  Proof.
    intros mm a w l n wr x xs Hf X0 X1 AP.
    assert (GEN : forall bs (P : mem -> Prop),
              bytes_at segs mm (zden E a) bs -> Z.of_nat (length bs) = Z.of_N w * zden E n ->
              (forall mm', (wr = true -> wr_at segs mm (zden E a) (Z.of_nat (length bs)) -> wr_at segs mm' (zden E a) (Z.of_nat (length bs))) ->
                           bytes_at segs mm' (zden E a) bs -> P mm') ->
              (wr = true -> wr_at segs mm (zden E a) (Z.of_nat (length bs))) ->
              P (write_to_mem mm (wa x) xs)).
    { intros bs P HB HL HP HW. apply HP.
      - intros Hwr HWR. apply wr_at_write. exact HWR.
      - destruct AP as [AP|AP].
        + assert (E0 : bs = []) by (destruct bs; [reflexivity| cbn in HL; lia]). subst bs.
          pose proof (bytes_at_bound _ _ _ _ HB). apply bytes_at_nil_any; cbn in *; lia.
        + apply bytes_at_write_other; [exact HB| exact X0| exact X1| lia]. }
    destruct (marr_cases w) as [-> |[-> |[-> | (N1 & N4 & N8)]]].
    - cbn -[u8arr bytes_at ldenb Z.of_nat Z.mul write_to_mem wa Z.pow] in Hf |- *. rewrite ?zdenp_ok in Hf |- *.
      destruct Hf as [H HL]. split; [|exact HL].
      apply (GEN (ldenb E l) (fun mm' => if wr then u8arr segs mm' (zden E a) (ldenb E l) else bytes_at segs mm' (zden E a) (ldenb E l))).
      + destruct wr; [exact (proj1 H)| exact H].
      + lia.
      + intros mm' HW HB. destruct wr; [split; [exact HB| apply HW; [reflexivity| exact (proj2 H)]]| exact HB].
      + intros ->. exact (proj2 H).
    - cbn -[u32arr bytes_at ldenw u32s Z.of_nat Z.mul write_to_mem wa Z.pow] in Hf |- *. rewrite ?zdenp_ok in Hf |- *.
      destruct Hf as [H HL]. split; [|exact HL].
      apply (GEN (u32s (ldenw E l)) (fun mm' => if wr then u32arr segs mm' (zden E a) (ldenw E l) else bytes_at segs mm' (zden E a) (u32s (ldenw E l)))).
      + destruct wr; [exact (proj1 H)| exact H].
      + rewrite u32s_length. lia.
      + intros mm' HW HB. destruct wr; [| exact HB]. split; [exact HB|].
        rewrite u32s_length in HW. replace (4 * Z.of_nat (length (ldenw E l))) with (Z.of_nat (4 * length (ldenw E l))) by lia.
        apply HW; [reflexivity|]. replace (Z.of_nat (4 * length (ldenw E l))) with (4 * Z.of_nat (length (ldenw E l))) by lia. exact (proj2 H).
      + intros ->. rewrite u32s_length. replace (Z.of_nat (4 * length (ldenw E l))) with (4 * Z.of_nat (length (ldenw E l))) by lia. exact (proj2 H).
    - cbn -[u64arr bytes_at ldenw u64s Z.of_nat Z.mul write_to_mem wa Z.pow] in Hf |- *. rewrite ?zdenp_ok in Hf |- *.
      destruct Hf as [H HL]. split; [|exact HL].
      apply (GEN (u64s (ldenw E l)) (fun mm' => if wr then u64arr segs mm' (zden E a) (ldenw E l) else bytes_at segs mm' (zden E a) (u64s (ldenw E l)))).
      + destruct wr; [exact (proj1 H)| exact H].
      + rewrite u64s_length. lia.
      + intros mm' HW HB. destruct wr; [| exact HB]. split; [exact HB|].
        rewrite u64s_length in HW. replace (8 * Z.of_nat (length (ldenw E l))) with (Z.of_nat (8 * length (ldenw E l))) by lia.
        apply HW; [reflexivity|]. replace (Z.of_nat (8 * length (ldenw E l))) with (8 * Z.of_nat (length (ldenw E l))) by lia. exact (proj2 H).
      + intros ->. rewrite u64s_length. replace (Z.of_nat (8 * length (ldenw E l))) with (8 * Z.of_nat (length (ldenw E l))) by lia. exact (proj2 H).
    - exfalso. cbn in Hf. destruct w as [|p]; [exact Hf|]. repeat (destruct p as [p|p|]; try exact (proj1 Hf); try exact Hf; try congruence).
  Qed.

  (* [comment removed for export] *)
  Lemma marr_transport : forall mm mm' W a w l n wr,
    mfact_ok segs L CS E mm (MArr a w l n wr) -> munch W mm mm' -> wmono segs mm mm' ->
    (zden E n <= 0 \/ disjoint_from W (zden E a) (Z.of_N w * zden E n)) ->
    mfact_ok segs L CS E mm' (MArr a w l n wr).
  Proof.
    intros mm mm' W a w l n wr Hf MU WM AP.
    assert (GEN : forall bs (P : mem -> Prop),
              bytes_at segs mm (zden E a) bs -> Z.of_nat (length bs) = Z.of_N w * zden E n ->
              (forall mm'', (wr = true -> wr_at segs mm (zden E a) (Z.of_nat (length bs)) -> wr_at segs mm'' (zden E a) (Z.of_nat (length bs))) ->
                            bytes_at segs mm'' (zden E a) bs -> P mm'') ->
              (wr = true -> wr_at segs mm (zden E a) (Z.of_nat (length bs))) ->
              P mm').
    { intros bs P HB HL HP HW. apply HP.
      - intros Hwr HWR. eapply wr_at_transport; [exact HWR| exact WM].
      - destruct AP as [AP|AP].
        + assert (E0 : bs = []) by (destruct bs; [reflexivity| cbn in HL; lia]). subst bs.
          pose proof (bytes_at_bound _ _ _ _ HB). apply bytes_at_nil_any; cbn in *; lia.
        + eapply bytes_at_transport; [exact HB| exact MU| rewrite HL; exact AP]. }
    destruct (marr_cases w) as [-> |[-> |[-> | (N1 & N4 & N8)]]].
    - cbn -[u8arr bytes_at ldenb Z.of_nat Z.mul Z.pow] in Hf |- *. rewrite ?zdenp_ok in Hf |- *.
      destruct Hf as [H HL]. split; [|exact HL].
      apply (GEN (ldenb E l) (fun mm'' => if wr then u8arr segs mm'' (zden E a) (ldenb E l) else bytes_at segs mm'' (zden E a) (ldenb E l))).
      + destruct wr; [exact (proj1 H)| exact H].
      + lia.
      + intros mm'' HW HB. destruct wr; [split; [exact HB| apply HW; [reflexivity| exact (proj2 H)]]| exact HB].
      + intros ->. exact (proj2 H).
    - cbn -[u32arr bytes_at ldenw u32s Z.of_nat Z.mul Z.pow] in Hf |- *. rewrite ?zdenp_ok in Hf |- *.
      destruct Hf as [H HL]. split; [|exact HL].
      apply (GEN (u32s (ldenw E l)) (fun mm'' => if wr then u32arr segs mm'' (zden E a) (ldenw E l) else bytes_at segs mm'' (zden E a) (u32s (ldenw E l)))).
      + destruct wr; [exact (proj1 H)| exact H].
      + rewrite u32s_length. lia.
      + intros mm'' HW HB. destruct wr; [| exact HB]. split; [exact HB|].
        rewrite u32s_length in HW. replace (4 * Z.of_nat (length (ldenw E l))) with (Z.of_nat (4 * length (ldenw E l))) by lia.
        apply HW; [reflexivity|]. replace (Z.of_nat (4 * length (ldenw E l))) with (4 * Z.of_nat (length (ldenw E l))) by lia. exact (proj2 H).
      + intros ->. rewrite u32s_length. replace (Z.of_nat (4 * length (ldenw E l))) with (4 * Z.of_nat (length (ldenw E l))) by lia. exact (proj2 H).
    - cbn -[u64arr bytes_at ldenw u64s Z.of_nat Z.mul Z.pow] in Hf |- *. rewrite ?zdenp_ok in Hf |- *.
      destruct Hf as [H HL]. split; [|exact HL].
      apply (GEN (u64s (ldenw E l)) (fun mm'' => if wr then u64arr segs mm'' (zden E a) (ldenw E l) else bytes_at segs mm'' (zden E a) (u64s (ldenw E l)))).
      + destruct wr; [exact (proj1 H)| exact H].
      + rewrite u64s_length. lia.
      + intros mm'' HW HB. destruct wr; [| exact HB]. split; [exact HB|].
        rewrite u64s_length in HW. replace (8 * Z.of_nat (length (ldenw E l))) with (Z.of_nat (8 * length (ldenw E l))) by lia.
        apply HW; [reflexivity|]. replace (Z.of_nat (8 * length (ldenw E l))) with (8 * Z.of_nat (length (ldenw E l))) by lia. exact (proj2 H).
      + intros ->. rewrite u64s_length. replace (Z.of_nat (8 * length (ldenw E l))) with (8 * Z.of_nat (length (ldenw E l))) by lia. exact (proj2 H).
    - exfalso. cbn in Hf. destruct w as [|p]; [exact Hf|]. repeat (destruct p as [p|p|]; try exact (proj1 Hf); try exact Hf; try congruence).
  Qed.

  Lemma pointwise_apart : forall a w b n, 0 < w -> 0 < n ->
    (forall z y, a <= z < a + w -> b <= y < b + n -> z <> y) -> b + n <= a \/ a + w <= b.
  Proof.
    intros a w b n Hw Hn H.
    destruct (Z_lt_le_dec a (b + n)); [|left; lia]. destruct (Z_lt_le_dec b (a + w)); [|right; lia]. exfalso.
    apply (H (Z.max a b) (Z.max a b)); lia.
  Qed.

  (* [comment removed for export] *)
  Lemma class_apart_sound : forall pf crs cl a w b n,
    Forall (pfact_ok CS E) pf ->
    Forall (fun an => crange CS (zden E (fst an)) (zden E (snd an))) crs ->
    acls_ok cl (zden E a) w ->
    class_apart C pf crs cl b n = true ->
    forall z y, zden E a <= z < zden E a + w -> zden E b <= y < zden E b + zden E n -> z <> y.
  Proof.
    intros pf crs cl a w b n HP HCR ACL H z y Hz Hy. unfold class_apart in H.
    destruct (c_acc C) as [A|] eqn:HCA; [|discriminate]. destruct (HACC A eq_refl) as (_ & _ & CSOK).
    pose proof CSOK as (C1 & _ & _ & _).
    destruct cl; try discriminate; cbn in ACL.
    - (* [comment removed for export] *)
      destruct (shadow_split (ac_sb A) b) as [[x kr]|] eqn:SS; [|discriminate]. apply andb_prop in H as [ALX IC].
      apply N.leb_le in ALX.
      apply (in_some_crange_sound pf crs) in IC; [|exact HP| exact HCR]. rewrite sh_c_den, emulc_den in IC.
      pose proof (shadow_addr L E A (HSB A eq_refl) b x kr SS) as SB. rewrite sh_c_den in SB. set (k := zden E kr) in *.
      pose proof (eal_sound E (mk_oracle pf) x (mk_oracle_sound CS E pf HP)) as ALS.
      assert (D8 : (8 | zden E x)).
      { eapply Z.divide_trans; [|exact ALS]. exists (2 ^ (Z.of_N (eal (mk_oracle pf) x) - 3)).
        change 8 with (2 ^ 3). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
      destruct D8 as [q Hq].
      intros ->. apply (C1 (zden E x + 8 * (k + (y - zden E b)))).
      + apply IC. lia.
      + replace (shadow_of L (zden E x + 8 * (k + (y - zden E b)))) with y; [apply ACL; exact Hz|].
        rewrite SB. unfold shadow_of. rewrite Hq.
        replace (q * 8 + 8 * k) with ((q + k) * 8) by lia. rewrite (Z.div_mul (q + k)) by lia.
        replace (q * 8 + 8 * (k + (y - (al_sb L + (q + k))))) with ((y - al_sb L) * 8) by lia. rewrite Z.div_mul by lia. lia.
    - (* [comment removed for export] *)
      apply (in_some_crange_sound pf crs) in H; [|exact HP| exact HCR].
      destruct (ACL (z - zden E a) ltac:(lia)) as (c & Hc & Hzc). replace (zden E a + (z - zden E a)) with z in Hzc by lia.
      intros ->. apply (C1 c Hc). rewrite <- Hzc. apply H. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma opq_iv_ok_sound : forall pf crs a n ok sh,
    Forall (pfact_ok CS E) pf ->
    Forall (fun an => crange CS (zden E (fst an)) (zden E (snd an))) crs ->
    opq_iv_ok C pf crs a n ok sh = true ->
    opq_allowed L CS (wden E ok) (wden E sh) (zden E a, zden E a + zden E n).
  Proof.
    intros pf crs a n ok sh HP HCR H.
    (* [comment removed for export] *)
    set (TOK := fun (test : expr -> expr -> expr -> expr -> bool) => forall a' n' b' k', test a' n' b' k' = true ->
                  zden E b' <= zden E a' /\ zden E a' + zden E n' <= zden E b' + zden E k').
    assert (T0 : TOK (fun a' n' b' k' => iv_inside_syn a' n' b' k')) by (intros a' n' b' k' T; exact (iv_inside_syn_sound E _ _ _ _ T)).
    assert (T1 : TOK (dec_inside0 pf)) by (intros a' n' b' k' T; exact (dec_inside0_sound CS E _ _ _ _ _ HP T)).
    assert (T2 : TOK (dec_inside pf)) by (intros a' n' b' k' T; exact (dec_inside_sound CS E _ _ _ _ _ HP T)).
    assert (OKC : forall test, TOK test -> opq_in test a n ok = true -> opq_allowed L CS (wden E ok) (wden E sh) (zden E a, zden E a + zden E n)).
    { intros test HT HO. left. unfold opq_in in HO. apply any_iv_exists in HO as (lo & hi & Hin & D). apply HT in D.
      rewrite eadd_den, emulc_den in D. cbn [fst snd] in D.
      exists (zdenp E lo), (zdenp E hi). split; [|rewrite !zdenp_ok; cbn [fst snd]; lia].
      unfold wden. apply in_map_iff. exists (lo, hi). split; [reflexivity| exact Hin]. }
    assert (SHC : forall test, TOK test -> opq_sh_ok C pf crs a n test sh = true -> opq_allowed L CS (wden E ok) (wden E sh) (zden E a, zden E a + zden E n)).
    2:{ unfold opq_iv_ok in H.
        destruct (opq_in (fun a' n' b' k' => iv_inside_syn a' n' b' k') a n ok) eqn:E0; [exact (OKC _ T0 E0)|].
        destruct (opq_sh_ok C pf crs a n (fun a' n' b' k' => iv_inside_syn a' n' b' k') sh) eqn:E1; [exact (SHC _ T0 E1)|].
        destruct (opq_in (dec_inside0 pf) a n ok) eqn:E2; [exact (OKC _ T1 E2)|].
        destruct (opq_sh_ok C pf crs a n (dec_inside0 pf) sh) eqn:E3; [exact (SHC _ T1 E3)|].
        destruct (opq_in (dec_inside pf) a n ok) eqn:E4; [exact (OKC _ T2 E4)| exact (SHC _ T2 H)]. }
    intros test HT HS. unfold opq_sh_ok in HS.
    - right. destruct (c_acc C) as [A|] eqn:HCA; [|discriminate].
      destruct (shadow_split (ac_sb A) a) as [[x kr]|] eqn:SS; [|discriminate].
      destruct (N.leb 3 (eal (mk_oracle pf) x)) eqn:ALX; [|discriminate]. apply N.leb_le in ALX.
      match type of HS with (if ?c then _ else _) = true => destruct c eqn:D; [|discriminate] end. rename HS into IC.
      apply (in_some_crange_sound pf crs) in IC; [|exact HP| exact HCR]. rewrite sh_c_den, emulc_den in IC.
      unfold opq_in in D. apply any_iv_exists in D as (lo & hi & Hin & D). apply HT in D.
      rewrite !eadd_den, !emulc_den, !sh_c_den in D. cbn [zden fst snd] in D.
      pose proof (shadow_addr L E A (HSB A eq_refl) a x kr SS) as SB. rewrite sh_c_den in SB. set (k := zden E kr) in *.
      pose proof (eal_sound E (mk_oracle pf) x (mk_oracle_sound CS E pf HP)) as ALS.
      assert (D8 : (8 | zden E x)).
      { eapply Z.divide_trans; [|exact ALS]. exists (2 ^ (Z.of_N (eal (mk_oracle pf) x) - 3)).
        change 8 with (2 ^ 3). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
      destruct D8 as [q Hq]. cbn [fst snd]. intros y Hy.
      exists (zden E x + 8 * (k + (y - zden E a))), (zdenp E lo), (zdenp E hi).
      split. { unfold wden. apply in_map_iff. exists (lo, hi). split; [reflexivity| exact Hin]. }
      rewrite !zdenp_ok. split; [lia|]. split; [apply IC; lia|].
      rewrite SB. unfold shadow_of. rewrite Hq.
      replace (q * 8 + 8 * k) with ((q + k) * 8) by lia. rewrite (Z.div_mul (q + k)) by lia.
      replace (q * 8 + 8 * (k + (y - (al_sb L + (q + k))))) with ((y - al_sb L) * 8) by lia. rewrite Z.div_mul by lia. lia.
  Qed.

  Lemma shadow_apart_sound : forall A pf a (w : N) oa on bs,
    zdenp E (ac_sb A) = al_sb L ->
    Forall (pfact_ok CS E) pf ->
    length bs = N.to_nat w -> 0 <= zden E a -> zden E a + Z.of_N w <= 2 ^ 64 -> 0 < Z.of_N w ->
    shadow_apart A pf a (Z.of_N w) oa on = true ->
    aobj segs L CS m (zden E oa) (zden E on) ->
    aobj segs L CS (write_to_mem m (wa (zden E a)) bs) (zden E oa) (zden E on).
  Proof.
    intros A pf a w oa on bs HCA HP LEN A0 A1 Wp H [HC HS].
    unfold shadow_apart in H.
    destruct (shadow_split (ac_sb A) a) as [[x kr]|] eqn:SS; [|discriminate].
    apply andb_prop in H as [ALX H]. apply N.leb_le in ALX. lazy zeta in H.
    pose proof (shadow_addr L E A HCA a x kr SS) as SB. rewrite sh_c_den in SB.
    pose proof (eal_sound E (mk_oracle pf) x (mk_oracle_sound CS E pf HP)) as ALS.
    assert (D8 : (8 | zden E x)).
    { eapply Z.divide_trans; [|exact ALS]. exists (2 ^ (Z.of_N (eal (mk_oracle pf) x) - 3)).
      change 8 with (2 ^ 3). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
    destruct D8 as [q Hq].
    assert (AP : zden E on <= 0 \/ zden E x + 8 * zden E kr + 8 * Z.of_N w <= zden E oa \/ zden E oa + zden E on <= zden E x + 8 * zden E kr).
    { destruct (sep_lookup true pf (sh_c x kr) (ELit (8 * Z.of_N w)) oa on) eqn:SL.
      { destruct (sep_lookup_sound CS E true pf _ _ _ _ HP SL) as [[_ X]|X]; rewrite ?sh_c_den in X; cbn [zden] in X; lia. }
      assert (X : Exists (fun e => 0 <= zden E e)
                [emulc (-1) on; sep_l (sh_c x kr) (ELit (8 * Z.of_N w)) oa; sep_r (sh_c x kr) oa on]).
      { destruct (lin_ge_list pf [emulc (-1) on; sep_l (sh_c x kr) (ELit (8 * Z.of_N w)) oa; sep_r (sh_c x kr) oa on]) eqn:L1.
        - apply (lin_ge_list_sound CS E) in L1; [exact L1| exact HP].
        - apply (lin_ge_listX_sound CS E) in H; [exact H| exact HP]. }
      apply Exists_cons in X. destruct X as [X|X]; [rewrite emulc_den in X; lia|].
      apply Exists_cons in X. destruct X as [X|X]; [rewrite sep_l_den, sh_c_den in X; cbn [zden] in X; lia|].
      apply Exists_cons in X. destruct X as [X|X]; [rewrite sep_r_den, sh_c_den in X; cbn [zden] in X; lia|].
      apply Exists_nil in X. contradiction. }
    set (k := zden E kr) in *.
    split; [exact HC|].
    intros c Hc. destruct (HS c Hc) as (kb & B & HK). exists kb. split; [|exact HK].
    apply bytes_at_write_other; [exact B| lia| rewrite LEN; lia|].
    cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]. rewrite LEN. replace (Z.of_nat (N.to_nat w)) with (Z.of_N w) by lia.
    rewrite SB. unfold shadow_of. rewrite Hq.
    replace (q * 8 + 8 * k) with ((q + k) * 8) by lia. rewrite Z.div_mul by lia.
    destruct AP as [AP|[AP|AP]]; [exfalso; lia| |].
    + right. assert (q + k + Z.of_N w <= c / 8) by (apply Z.div_le_lower_bound; lia). lia.
    + left. assert (c / 8 < q + k) by (apply Z.div_lt_upper_bound; lia). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma hpr_iv_ok_out : forall pf mf blo bln ok b n x,
    Forall (pfact_ok CS E) pf -> Forall (mfact_ok segs L CS E m) mf ->
    hp_blk (ecw E) ->
    Forall (fun iv => forall x, fst iv <= x < snd iv -> forall LB', (forall b0, In b0 (elb0 E) -> In b0 LB') -> ecw E LB' x) (wden E ok) ->
    (forall b0, In b0 (elb0 E) -> In b0 (blden E blo)) ->
    hpr_iv_ok pf mf blo bln ok b n = true ->
    in_block (blden E bln) x -> ~ ecw E (blden E blo) x -> ~ (zden E b <= x < zden E b + zden E n).
  Proof.
    intros pf mf blo bln ok b n x HP HMF HBK' HCW HI0 H HIN HNCW HX. unfold hpr_iv_ok in H.
    destruct (ivs_cover pf b n ok) eqn:IC.
    - destruct (ivs_cover_sound pf b n ok HP IC) as (lo & hi & Hin & Hlo & Hhi).
      apply HNCW. rewrite List.Forall_forall in HCW. apply (HCW (lo, hi) Hin); [cbn [fst snd]; lia| exact HI0].
    - destruct (bl_covers pf blo b n) eqn:BC.
      + destruct (bl_covers_sound pf blo b n HP BC) as (ba & bk & Hin & Hlo & Hhi).
        apply HNCW. apply (HBK' (blden E blo) (zden E ba) (zden E bk) x Hin). lia.
      + exact (apart_covers_sound pf mf bln b n x HP HMF H HX HIN).
  Qed.

  Lemma mf_survives_sound : forall pf crs mf cl a (w : N) f bs,
    Forall (pfact_ok CS E) pf ->
    Forall (fun an => crange CS (zden E (fst an)) (zden E (snd an))) crs ->
    Forall (mfact_ok segs L CS E m) mf ->
    acls_ok cl (zden E a) (Z.of_N w) -> okw w = true ->
    length bs = N.to_nat w -> 0 <= zden E a -> zden E a + Z.of_N w <= 2 ^ 64 ->
    mem_inv segs (write_to_mem m (wa (zden E a)) bs) ->
    mf_survives C pf crs mf cl a (Z.of_N w) f = true ->
    mfact_ok segs L CS E m f ->
    mfact_ok segs L CS E (write_to_mem m (wa (zden E a)) bs) f.
  Proof.
    intros pf crs mf cl a w f bs HP HCR HMF ACL OKW LEN A0 A1 MI2 H Hf.
    pose proof HSB as HSB0.
    assert (Wpos : 0 < Z.of_N w) by (destruct (okw_cases w OKW) as [-> |[-> |[-> | ->]]]; lia).
    (* [comment removed for export] *)
    assert (CLS : forall b n, (Z.ltb 0 n && class_apart C pf crs cl b (ELit n)) = true ->
              zden E b + n <= zden E a \/ zden E a + Z.of_nat (length bs) <= zden E b).
    { intros b n Hc. apply andb_prop in Hc as [Hn Hc]. apply Z.ltb_lt in Hn. rewrite LEN.
      replace (Z.of_nat (N.to_nat w)) with (Z.of_N w) by lia. apply pointwise_apart; [lia| lia|].
      intros z y Hz Hy. apply (class_apart_sound pf crs cl a (Z.of_N w) b (ELit n) HP HCR ACL Hc z y Hz). cbn [zden]. lia. }
    destruct f as [b cs|b cs|b n k|lo hi|oa on|ok_k ok_l sh_l|ra_ rw_ rl_ rn_ rwr_|mW mi mj|mi mj|ml mX mi mj|ml ma mn|ml ma mn|qbl qok|ql qbl qsp qX qi qj|ql qs qa qn|qa qn qbl|ql qk|qj qo qn qxs qok]; cbn [mf_survives] in H.
    7:{ (* [comment removed for export] *)
        lazy zeta in H.
        assert (Wd : 0 < Z.of_N rw_) by (destruct (marr_cases rw_) as [-> |[-> |[-> |(N1 & N4 & N8)]]]; try lia;
          exfalso; cbn in Hf; destruct rw_ as [|p]; [exact Hf|]; repeat (destruct p as [p|p|]; try exact (proj1 Hf); try exact Hf; try congruence)).
        assert (X : Exists (fun e => 0 <= zden E e) [emulc (-1) rn_; sep_l a (ELit (Z.of_N w)) ra_; sep_r a ra_ (emulc (Z.of_N rw_) rn_)]).
        { destruct (sep_lookup true pf a (ELit (Z.of_N w)) ra_ (emulc (Z.of_N rw_) rn_)) eqn:SL.
          { destruct (sep_lookup_sound CS E true pf _ _ _ _ HP SL) as [[_ X]|[X|X]]; cbn [zden] in X; rewrite ?emulc_den in X.
            - apply Exists_cons_hd. rewrite emulc_den. nia.
            - apply Exists_cons_tl, Exists_cons_hd. rewrite sep_l_den. cbn [zden]. lia.
            - apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd. rewrite sep_r_den, emulc_den. lia. }
          destruct (class_apart C pf crs cl ra_ (emulc (Z.of_N rw_) rn_)) eqn:CA.
          { destruct (Z_lt_le_dec 0 (zden E rn_)) as [Hn|Hn].
            * assert (AP : zden E ra_ + Z.of_N rw_ * zden E rn_ <= zden E a \/ zden E a + Z.of_nat (length bs) <= zden E ra_).
              { rewrite LEN. replace (Z.of_nat (N.to_nat w)) with (Z.of_N w) by lia. apply pointwise_apart; [lia| nia|].
                intros z y Hz Hy. apply (class_apart_sound pf crs cl a (Z.of_N w) ra_ (emulc (Z.of_N rw_) rn_) HP HCR ACL CA z y Hz).
                rewrite emulc_den. exact Hy. }
              destruct AP as [AP|AP].
              -- apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd. rewrite sep_r_den, emulc_den. lia.
              -- apply Exists_cons_tl, Exists_cons_hd. rewrite sep_l_den. cbn [zden]. rewrite LEN in AP. lia.
            * apply Exists_cons_hd. rewrite emulc_den. lia. }
          destruct (lin_ge_list pf [emulc (-1) rn_; sep_l a (ELit (Z.of_N w)) ra_; sep_r a ra_ (emulc (Z.of_N rw_) rn_)]) eqn:L1.
          - apply (lin_ge_list_sound CS E) in L1; [exact L1|exact HP].
          - apply (lin_ge_listX_sound CS E) in H; [exact H|exact HP]. }
        clear H.
        apply (marr_frame m ra_ rw_ rl_ rn_ rwr_ (zden E a) bs Hf A0); [rewrite LEN; lia|].
        apply Exists_cons in X. destruct X as [X|X]; [left; rewrite emulc_den in X; lia|].
        apply Exists_cons in X. destruct X as [X|X]; [right; right; rewrite sep_l_den in X; cbn [zden] in X; rewrite LEN; lia|].
        apply Exists_cons in X. destruct X as [X|X]; [right; left; rewrite sep_r_den, emulc_den in X; lia|].
        apply Exists_nil in X. contradiction. }
    all: cbn in Hf |- *; rewrite ?zdenp_ok in Hf |- *.
    - assert (AP : zden E b + Z.of_nat (cells_size (csden E cs)) <= zden E a \/ zden E a + Z.of_nat (length bs) <= zden E b).
      { unlazy1_in H. destruct ((0 <? Z.of_N (cells_sizeN cs)) && class_apart C pf crs cl b (ELit (Z.of_N (cells_sizeN cs)))) eqn:CA.
        - apply CLS in CA. rewrite csden_size. lia.
        - apply (dec_apart_sound CS E _ _ _ _ _ HP) in H. cbn [zden] in H. rewrite csden_size in *. rewrite LEN. lia. }
      apply rw_cells_frame; [exact Hf| lia | rewrite LEN; lia | exact AP].
    - assert (AP : zden E b + Z.of_nat (cells_size (csden E cs)) <= zden E a \/ zden E a + Z.of_nat (length bs) <= zden E b).
      { match type of H with (if ?st then true else _) = true => destruct st eqn:HST end.
        2:{ unlazy1_in H. destruct ((0 <? Z.of_N (cells_sizeN cs)) && class_apart C pf crs cl b (ELit (Z.of_N (cells_sizeN cs)))) eqn:CA.
            - apply CLS in CA. rewrite csden_size. lia.
            - apply (dec_apart_sound CS E _ _ _ _ _ HP) in H. cbn [zden] in H. rewrite csden_size in *. rewrite LEN. lia. }
        clear H. rename HST into H.
        - (* [comment removed for export] *)
          assert (Hcl : cl = AcClient \/ cl = AcShadow) by (destruct cl; [left|right|discriminate]; reflexivity).
          assert (H' : is_static C b && N.eqb (cells_sizeN cs) 8 = true) by (destruct cl; [exact H|exact H|discriminate]).
          clear H. apply andb_prop in H' as [H S8]. apply N.eqb_eq in S8.
          unfold is_static in H. destruct (c_acc C) as [A|] eqn:HCA; [|discriminate].
          destruct (HACC A eq_refl) as (Hgot & Hgsb & CSOK).
          destruct (is_lit b) as [z|] eqn:LB; [|discriminate]. apply is_lit_den with (E := E) in LB.
          rewrite csden_size, S8, LEN, LB. cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
          replace (Z.of_nat (N.to_nat w)) with (Z.of_N w) by lia.
          apply orb_prop in H; rewrite Hgot, Hgsb in H.
          eapply static_apart; [exact CSOK| exact Hcl| exact ACL| |lia].
          destruct H as [H|H]; apply Z.eqb_eq in H; [left|right]; exact H. }
      apply ro_cells_frame; [exact Hf| lia | rewrite LEN; lia | exact AP].
    - destruct Hf as [HB HL].
      (* [comment removed for export] *)
      assert (H' : Exists (fun e => 0 <= zden E e) [emulc (-1) n; sep_l a (ELit (Z.of_N w)) b; sep_r a b n]).
      { destruct (sep_lookup true pf a (ELit (Z.of_N w)) b n) eqn:SL.
        { destruct (sep_lookup_sound CS E true pf _ _ _ _ HP SL) as [[_ X]|[X|X]]; cbn [zden] in X.
          - apply Exists_cons_hd. rewrite emulc_den. lia.
          - apply Exists_cons_tl, Exists_cons_hd. rewrite sep_l_den. cbn [zden]. lia.
          - apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd. rewrite sep_r_den. lia. }
        destruct (class_apart C pf crs cl b n) eqn:CA.
        { destruct (Z_lt_le_dec 0 (zden E n)) as [Hn|Hn].
          * assert (AP : zden E b + zden E n <= zden E a \/ zden E a + Z.of_nat (length bs) <= zden E b).
            { rewrite LEN. replace (Z.of_nat (N.to_nat w)) with (Z.of_N w) by lia. apply pointwise_apart; [lia| lia|].
              intros z y Hz Hy. apply (class_apart_sound pf crs cl a (Z.of_N w) b n HP HCR ACL CA z y Hz Hy). }
            destruct AP as [AP|AP].
            -- apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd. rewrite sep_r_den. lia.
            -- apply Exists_cons_tl, Exists_cons_hd. rewrite sep_l_den. cbn [zden]. rewrite LEN in AP. lia.
          * apply Exists_cons_hd. rewrite emulc_den. lia. }
        destruct (lin_ge_list pf [emulc (-1) n; sep_l a (ELit (Z.of_N w)) b; sep_r a b n]) eqn:L1.
        - apply (lin_ge_list_sound CS E) in L1; [exact L1|exact HP].
        - apply (lin_ge_listX_sound CS E) in H; [exact H|exact HP]. }
      clear H. rename H' into H.
      split; [|exact HL].
      apply Exists_cons in H. destruct H as [H|H].
      + rewrite emulc_den in H. assert (eb E k = []) as -> by (destruct (eb E k); [reflexivity| cbn in HL; lia]).
        pose proof (bytes_at_bound _ _ _ _ HB). apply bytes_at_nil_any; cbn in *; lia.
      + apply Exists_cons in H. destruct H as [H|H].
        * rewrite sep_l_den in H. cbn [zden] in H. apply bytes_at_write_other; [exact HB| lia| rewrite LEN; lia| rewrite LEN; lia].
        * apply Exists_cons in H. destruct H as [H|H]; [|apply Exists_nil in H; contradiction].
          rewrite sep_r_den in H. apply bytes_at_write_other; [exact HB| lia| rewrite LEN; lia| rewrite LEN; lia].
    - apply stk_write; [exact Hf| lia| rewrite LEN; lia].
    - destruct (c_acc C) as [A|] eqn:HCA; [|discriminate]. destruct (HACC A eq_refl) as (_ & _ & CSOK).
      destruct cl; try discriminate.
      + cbn in ACL. apply aobj_frame; [exact CSOK| exact Hf| rewrite LEN | lia | rewrite LEN; lia].
        replace (Z.of_nat (N.to_nat w)) with (Z.of_N w) by lia. exact ACL.
      + (* [comment removed for export] *)
        exact (shadow_apart_sound A pf a w oa on bs (HSB0 A eq_refl) HP LEN A0 A1 Wpos H Hf).
    - (* [comment removed for export] *)
      destruct Hf as [HPm LAW]. split; [|exact LAW].
      apply (LAW [(zden E a, zden E a + Z.of_N w)] m).
      + exact HPm.
      + apply (munch_write _ m m); [apply munch_refl| lia| rewrite LEN; lia| cbn; left; rewrite LEN; lia].
      + intros x Hx. apply wview_write_mono. exact Hx.
      + constructor; [|constructor]. cbn [fst snd].
        exact (opq_iv_ok_sound pf crs a (ELit (Z.of_N w)) ok_l sh_l HP HCR H).
    (* [comment removed for export] *)
    - exact Hf. - exact Hf. - exact Hf. - exact Hf. - exact Hf.
    - (* [comment removed for export] *)
      destruct Hf as [[HPm HCW] HREST]. split; [|exact HREST]. split; [|exact HCW].
      apply (HPF (blden E qbl) m _ (ecur E) [(zden E a, zden E a + Z.of_N w)] HPm).
      + apply (munch_write _ m m); [apply munch_refl| lia| rewrite LEN; lia| cbn; left; rewrite LEN; lia].
      + intros x Hx. apply wview_write_mono. exact Hx.
      + constructor; [|constructor]. cbn [fst snd]. intros x Hx.
        destruct (opq_iv_ok C pf crs a (ELit (Z.of_N w)) qok []) eqn:OKI.
        * pose proof (opq_iv_ok_sound pf crs a (ELit (Z.of_N w)) qok [] HP HCR OKI) as X. cbn [zden] in X.
          destruct X as [(lo & hi & Hin & Hlo & Hhi)|X]; [cbn [fst snd] in Hlo, Hhi|].
          2:{ exfalso. destruct (X (zden E a) ltac:(cbn [fst snd]; lia)) as (c & lo & hi & [] & _). }
          rewrite List.Forall_forall in HCW. apply (HCW (lo, hi)); [| cbn [fst snd]; lia| exact (proj1 HREST)].
          unfold wden. apply in_map_iff. unfold wden in Hin. apply in_map_iff in Hin. exact Hin.
        * destruct (bl_covers_sound pf qbl a (ELit (Z.of_N w)) HP H) as (ba & bk & Hin & Hlo & Hhi). cbn [zden] in Hhi.
          apply (HBK (blden E qbl) (zden E ba) (zden E bk) x Hin). lia.
    - exact Hf. - exact Hf. - exact Hf. - exact Hf.
    - (* [comment removed for export] *)
      destruct Hf as [HR (HOK & HBK' & HCW & HI0 & HI1)]. split; [| exact (conj HOK (conj HBK' (conj HCW (conj HI0 HI1))))].
      apply (HOK _ _ _ m _ HR MI2). intros x Hx HIN HNCW.
      pose proof (hpr_iv_ok_out pf mf qo qn qok a (ELit (Z.of_N w)) x HP HMF HBK' HCW HI0 H HIN HNCW) as OUT. cbn [zden] in OUT.
      split.
      + pose proof (munch_write [(zden E a, zden E a + Z.of_N w)] m m (zden E a) bs (munch_refl _ _) ltac:(lia) ltac:(rewrite LEN; lia)
                      ltac:(cbn; left; rewrite LEN; lia)) as MW.
        apply MW. cbn. rewrite wa_unsigned by lia. lia.
      + intros V. apply wview_write_mono. exact V.
  Qed.
  (* [comment removed for export] *)
  Lemma wlog_pow : forall w, 0 < wlog w -> 2 ^ wlog w = w.
  Proof. intros w H. unfold wlog in *. destruct w as [|p|p]; try lia. repeat (destruct p as [p|p|]; try lia; try reflexivity). Qed.

  Lemma terms_divc_den : forall O w ts ts', osound E O -> 0 < w -> terms_divc O w ts = Some ts' -> tden E ts = w * tden E ts'.
  Proof.
    intros O w ts. induction ts as [|[k a] ts IH]; intros ts' HO Hw H; cbn in H.
    - injection H; intros <-. cbn. lia.
    - destruct (Z.eqb_spec (k mod w) 0).
      + destruct (terms_divc O w ts) as [r|] eqn:TD; [|discriminate]. injection H; intros <-. cbn.
        rewrite (IH r HO Hw eq_refl). pose proof (Z.div_mod k w ltac:(lia)) as D. rewrite e, Z.add_0_r in D.
        rewrite D at 1. rewrite Z.mul_add_distr_l, Z.mul_assoc. reflexivity.
      + destruct (Z.ltb 0 (wlog w) && N.leb (Z.to_N (wlog w)) (eal O a)) eqn:AL; [|discriminate].
        apply andb_prop in AL as [WL AL]. apply Z.ltb_lt in WL. apply N.leb_le in AL.
        destruct (terms_divc O w ts) as [r|] eqn:TD; [|discriminate]. injection H; intros <-. cbn [tden fst snd].
        rewrite (IH r HO Hw eq_refl). cbn [zden opden]. rewrite Z.shiftr_div_pow2 by lia.
        pose proof (eal_sound E O a HO) as D2.
        assert (DW : (w | zden E a)).
        { eapply Z.divide_trans; [|exact D2]. rewrite <- (wlog_pow w WL). exists (2 ^ (Z.of_N (eal O a) - wlog w)).
          rewrite <- Z.pow_add_r by lia. f_equal. lia. }
        destruct DW as [q Hq]. rewrite Hq, (wlog_pow w WL), Z.div_mul by lia. lia.
  Qed.

  Lemma ediv_exact_den : forall O w d i, osound E O -> ediv_exact O w d = Some i -> zden E d = Z.of_N w * zden E i.
  Proof.
    intros O w d i HO H. unfold ediv_exact in H.
    destruct (Z.eqb_spec (Z.of_N w) 1) as [W1|W1]. { injection H; intros <-. lia. }
    destruct (Z.leb_spec (Z.of_N w) 0) as [W0|W0]; [discriminate|].
    destruct (lin_of d) as [ts c] eqn:LD.
    destruct (Z.eqb_spec (c mod Z.of_N w) 0); [|discriminate].
    destruct (terms_divc O (Z.of_N w) ts) as [ts'|] eqn:TD; [|discriminate]. injection H; intros <-.
    rewrite of_terms_den. pose proof (lin_of_den E d) as LL. rewrite LD in LL. cbn [fst snd] in LL.
    rewrite (terms_divc_den _ _ _ _ HO W0 TD) in LL. pose proof (Z.div_mod c (Z.of_N w) ltac:(lia)) as D. rewrite e, Z.add_0_r in D. lia.
  Qed.

  Lemma cell_expr_bytes : forall c v, cell_expr_of c = Some v -> okw (cellx_size c) = true ->
    cbytes (cden E c) = wbytes (cellx_size c) (Z_to_bv 64 (zdenp E v)).
  Proof.
    intros c v H OK. destruct c as [i|w e|w k|w i|c o l|w e]; cbn in H; try discriminate; injection H; intros <-.
    - cbn. rewrite w64_of_unsigned. reflexivity.
    - cbn in OK. destruct (okw_cases w OK) as [-> |[-> |[-> | ->]]]; cbn -[le8 le4 le2 le1 Z_to_bv zdenp]; rewrite <- ?le1_lit; reflexivity.
  Qed.

  Lemma store_hit_sound : forall pf a w c f tgt,
    Forall (pfact_ok CS E) pf -> mfact_ok segs L CS E m f ->
    okw w = true -> cellx_size c = w -> cell_wf (cden E c) ->
    store_hit pf a w c f = Some (Some tgt) ->
    store_ok segs m (wa (zden E a)) (N.to_nat w) = true
    /\ 0 <= zden E a /\ zden E a + Z.of_N w <= 2 ^ 64
    /\ Forall (mfact_ok segs L CS E (write_to_mem m (wa (zden E a)) (cbytes (cden E c)))) tgt.
  Proof.
    intros pf a w c f tgt HP Hf OKW SZ WF H.
    assert (LEN : length (cbytes (cden E c)) = N.to_nat w) by (rewrite cbytes_length, cden_size, SZ by exact WF; reflexivity).
    destruct f as [base cs|base cs|b n k|lo hi|oa on|ok_k ok_l sh_l|ra_ rw_ rl_ rn_ rwr_|mW mi mj|mi mj|ml mX mi mj|ml ma mn|ml ma mn|qbl qok|ql qbl qsp qX qi qj|ql qs qa qn|qa qn qbl|ql qk|qj qo qn qxs qok]; cbn [store_hit] in H; try discriminate.
    3:{ (* [comment removed for export] *)
        destruct rwr_; [|discriminate].
        destruct (arr_store pf a w c ra_ rw_ rl_ rn_) as [f'|] eqn:AS; [|discriminate].
        injection H; intros <-.
        unfold arr_store in AS. destruct (cell_expr_of c) as [v|] eqn:CE; [|discriminate].
        pose proof (cell_expr_bytes c v CE ltac:(rewrite SZ; exact OKW)) as BY. rewrite SZ in BY.
        rewrite BY.
        assert (Wpos : 0 < Z.of_N w) by (destruct (okw_cases w OKW) as [-> |[-> |[-> | ->]]]; lia).
        assert (LW : length (wbytes w (Z_to_bv 64 (zdenp E v))) = N.to_nat w) by (rewrite <- BY; exact LEN).
        rewrite zdenp_ok in LW |- *.
        destruct (N.eqb_spec rw_ 1) as [W1|W1].
        - (* [comment removed for export] *) subst rw_.
          destruct (dec_inside pf (esub a ra_) (ELit (Z.of_N w)) (ELit 0) rn_) eqn:DI; [|discriminate]. injection AS; intros <-.
          apply (dec_inside_sound CS E _ _ _ _ _ HP) in DI. rewrite esub_den in DI. cbn [zden] in DI.
          cbn [mfact_ok] in Hf. rewrite ?zdenp_ok in Hf. destruct Hf as [[HB HW] HL].
          pose proof (bytes_at_bound _ _ _ _ HB) as BB.
          split. { replace (zden E a) with (zden E ra_ + (zden E a - zden E ra_)) by lia. eapply wr_at_store_ok; [exact HW| lia| lia]. }
          split; [lia|]. split; [lia|].
          constructor; [|constructor]. cbn [mfact_ok ldenb]. rewrite ?zdenp_ok, esub_den.
          split.
          + split.
            * replace (zden E a) with (zden E ra_ + (zden E a - zden E ra_)) at 1 by lia. apply bytes_at_write_inside; [exact HB| lia| rewrite LW; lia].
            * rewrite upd_bytes_length by (rewrite LW; lia). apply wr_at_write. exact HW.
          + rewrite upd_bytes_length by (rewrite LW; lia). exact HL.
        - destruct (N.eqb_spec w rw_) as [<-|NEQ].
          2:{ (* [comment removed for export] *)
              destruct (N.eqb w 8 && N.eqb rw_ 4) eqn:W84; [|discriminate].
              apply andb_prop in W84 as [W8 W4]. apply N.eqb_eq in W8. apply N.eqb_eq in W4. subst rw_. rewrite W8 in *. clear W8 NEQ.
              destruct (ediv_exact (mk_oracle pf) 4 (esub a ra_)) as [i|] eqn:ED; [|discriminate].
              destruct (dec_inside pf i (ELit 2) (ELit 0) rn_) eqn:DI; [|discriminate]. injection AS; intros <-.
              apply (dec_inside_sound CS E _ _ _ _ _ HP) in DI. cbn [zden] in DI.
              apply (ediv_exact_den (mk_oracle pf)) in ED; [|exact (mk_oracle_sound CS E pf HP)]. rewrite esub_den in ED. cbn [Z.of_N] in ED.
              cbn [mfact_ok] in Hf. rewrite ?zdenp_ok in Hf. destruct Hf as [HU HL].
              pose proof (u32arr_bound _ _ _ _ HU) as BB.
              split. { replace (wa (zden E a)) with (wa (zden E ra_ + 4 * zden E i)) by (f_equal; lia).
                       apply (wr_at_store_ok segs m (zden E ra_) _ (4 * zden E i) 8 (proj2 HU)); lia. }
              split; [lia|]. split; [lia|].
              constructor; [|constructor]. cbn [mfact_ok ldenw wbytes]. rewrite ?zdenp_ok, eadd_den. cbn [zden].
              split; [| rewrite !upd_length; exact HL].
              replace (zden E a) with (zden E ra_ + 4 * zden E i) by lia.
              replace (Z.to_nat (zden E i + 1)) with (Z.to_nat (zden E i + 1)) by reflexivity.
              rewrite (eshr_den E (mk_oracle pf) (mk_oracle_sound CS E pf HP) v 32) by lia.
              rewrite (Z_to_bv_unsigned 64 (zden E v)) at 1.
              replace (Z_to_bv 64 (Z.shiftr (zlow 64 (zden E v)) 32)) with (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (zden E v) : word)) 32))
                by (rewrite Z_to_bv_unsigned; reflexivity).
              apply u32arr_write2; [exact HU| lia| lia]. }
          destruct (ediv_exact (mk_oracle pf) w (esub a ra_)) as [i|] eqn:ED; [|discriminate].
          destruct (dec_inside pf i (ELit 1) (ELit 0) rn_) eqn:DI; [|discriminate]. injection AS; intros <-.
          apply (dec_inside_sound CS E _ _ _ _ _ HP) in DI. cbn [zden] in DI.
          apply (ediv_exact_den (mk_oracle pf)) in ED; [|exact (mk_oracle_sound CS E pf HP)]. rewrite esub_den in ED.
          destruct (marr_cases w) as [-> |[-> |[-> |(N1 & N4 & N8)]]]; [congruence| | |].
          + (* [comment removed for export] *) cbn [mfact_ok] in Hf. rewrite ?zdenp_ok in Hf. destruct Hf as [HU HL].
            pose proof (u32arr_bound _ _ _ _ HU) as BB. cbn [Z.of_N] in ED.
            split. { apply (u32arr_store_ok segs m (zden E ra_) (ldenw E rl_) (zden E i)); [exact HU| lia| f_equal; lia]. }
            split; [lia|]. split; [lia|].
            constructor; [|constructor]. cbn [mfact_ok ldenw wbytes]. rewrite ?zdenp_ok.
            split; [| rewrite upd_length; exact HL].
            replace (zden E a) with (zden E ra_ + 4 * zden E i) by lia. apply u32arr_write; [exact HU| lia].
          + (* [comment removed for export] *) cbn [mfact_ok] in Hf. rewrite ?zdenp_ok in Hf. destruct Hf as [HU HL].
            pose proof (u64arr_bound _ _ _ _ HU) as BB. cbn [Z.of_N] in ED.
            split. { apply (u64arr_store_ok segs m (zden E ra_) (ldenw E rl_) (zden E i)); [exact HU| lia| f_equal; lia]. }
            split; [lia|]. split; [lia|].
            constructor; [|constructor]. cbn [mfact_ok ldenw wbytes]. rewrite ?zdenp_ok.
            split; [| rewrite upd_length; exact HL].
            replace (zden E a) with (zden E ra_ + 8 * zden E i) by lia. apply u64arr_write; [exact HU| lia].
          + exfalso. cbn in Hf. destruct w as [|p]; [exact Hf|]. repeat (destruct p as [p|p|]; try exact (proj1 Hf); try exact Hf; try congruence).
    }
    - (* [comment removed for export] *)
      destruct (ediff_litO (mk_oracle pf) a base) as [off|] eqn:HD; [|discriminate].
      destruct (Z.leb_spec 0 off); [|discriminate].
      destruct (Z.leb_spec (off + Z.of_N w) (Z.of_N (cells_sizeN cs))); [|discriminate]. cbn [andb] in H.
      destruct (cell_store cs off c) as [cs'|] eqn:CSO; [|discriminate]. injection H; intros <-.
      pose proof (mk_oracle_sound CS E pf HP) as HOd. apply (ediff_litO_den E (mk_oracle pf) a base off HOd) in HD. clear HOd.
      cbn in Hf. rewrite zdenp_ok in Hf.
      pose proof (rw_cells_bound _ _ _ _ Hf) as BND. rewrite csden_size in BND.
      pose proof Hf as [[WFcs HB] WR].
      destruct (cell_store_sound E cs off c cs' CSO WFcs WF) as (O0 & O1 & WF' & BY').
      pose proof (csden_wf_bytes_length E cs WFcs) as BLEN.
      assert (EA : zden E a = zden E base + Z.of_nat (Z.to_nat off)) by lia.
      split.
      { rewrite EA. eapply wr_at_store_ok; [exact WR| lia |]. rewrite csden_size. lia. }
      split; [lia|]. split; [lia|].
      constructor; [|constructor]. cbn. rewrite zdenp_ok.
        (* [comment removed for export] *)
        set (B := cells_bytes (csden E cs)) in *.
        assert (SPLIT : B = firstn (Z.to_nat off) B ++ firstn (N.to_nat w) (skipn (Z.to_nat off) B) ++ skipn (Z.to_nat off + N.to_nat w) B).
        { rewrite <- (firstn_skipn (Z.to_nat off) B) at 1.
          rewrite <- (firstn_skipn (N.to_nat w) (skipn (Z.to_nat off) B)) at 1.
          rewrite skipn_skipn. f_equal. f_equal. f_equal. lia. }
        assert (LB1 : length (firstn (Z.to_nat off) B) = Z.to_nat off) by (rewrite firstn_length; lia).
        assert (LB2 : length (firstn (N.to_nat w) (skipn (Z.to_nat off) B)) = N.to_nat w) by (rewrite firstn_length, skipn_length; lia).
        split.
        * split; [exact WF'|]. rewrite BY', SZ. rewrite SPLIT in HB at 1.
          apply bytes_at_app in HB as [HB1 HB23]. apply bytes_at_app in HB23 as [HB2 HB3]. rewrite LB1 in HB2, HB3. rewrite LB2 in HB3.
          apply bytes_at_app. split.
          { apply bytes_at_write_other; [exact HB1| lia| rewrite LEN; lia| rewrite LB1; lia]. }
          rewrite LB1. apply bytes_at_app. split.
          { replace (zden E base + Z.of_nat (Z.to_nat off)) with (zden E a) by lia.
            apply bytes_at_write_same; [lia| rewrite LEN; lia]. }
          rewrite LEN. eapply bytes_at_write_other; [exact HB3| lia| rewrite LEN; lia| rewrite LEN; lia].
        * (* [comment removed for export] *)
          assert (SZ' : Z.of_nat (cells_size (csden E cs')) = Z.of_nat (cells_size (csden E cs))).
          { rewrite <- !csden_wf_bytes_length0 by assumption. rewrite BY', !app_length, firstn_length, skipn_length, LEN, SZ. subst B. lia. }
          rewrite SZ'. apply wr_at_write. exact WR.
    - (* [comment removed for export] *)
      destruct (dec_inside pf a (ELit (Z.of_N w)) lo (eadd hi (emulc (-1) lo))) eqn:DI; [|discriminate].
      injection H; intros <-.
      apply (dec_inside_sound CS E _ _ _ _ _ HP) in DI. rewrite eadd_den, emulc_den in DI. cbn [zden] in DI.
      assert (D1 : zden E lo <= zden E a) by lia. assert (D2 : zden E a + Z.of_N w <= zden E hi) by lia. clear DI.
      cbn in Hf. rewrite !zdenp_ok in Hf. pose proof Hf as (ST1 & ST2 & ST).
      assert (Wpos : 0 < Z.of_N w) by (destruct (okw_cases w OKW) as [-> |[-> |[-> | ->]]]; lia).
      pose proof (stk_wr_at m _ _ (zden E a) (Z.of_N w) Hf D1 D2 ltac:(lia)) as WR.
      split. { replace (wa (zden E a)) with (wa (zden E a + 0)) by (f_equal; lia). eapply wr_at_store_ok; [exact WR| lia| lia]. }
      split; [lia|]. split; [lia|].
      constructor; [|constructor; [|constructor; [|constructor]]]; cbn; rewrite ?zdenp_ok, ?eadd_den; cbn [zden].
        * (* [comment removed for export] *) split.
          -- split; [cbn; split; [exact WF| exact I]|]. cbn [csden map cells_bytes]. rewrite app_nil_r.
             apply bytes_at_write_same; [lia| rewrite LEN; lia].
          -- cbn [csden map cells_size]. rewrite cden_size, SZ, Nat.add_0_r.
             apply wr_at_write. replace (Z.of_nat (N.to_nat w)) with (Z.of_N w) by lia. exact WR.
        * destruct (stk_split segs m _ (zden E a) _ Hf ltac:(lia)) as [SL _]. apply stk_write; [exact SL| lia| rewrite LEN; lia].
        * destruct (stk_split segs m _ (zden E a + Z.of_N w) _ Hf ltac:(lia)) as [_ SR]. apply stk_write; [exact SR| lia| rewrite LEN; lia].
  Qed.

  Lemma store_target_pass_sound : forall chunks pf mf a w c tgt rest,
    Forall (pfact_ok CS E) pf -> Forall (mfact_ok segs L CS E m) mf ->
    okw w = true -> cellx_size c = w -> cell_wf (cden E c) ->
    store_target_pass chunks pf mf a w c = Some (tgt, rest) ->
    store_ok segs m (wa (zden E a)) (N.to_nat w) = true
    /\ 0 <= zden E a /\ zden E a + Z.of_N w <= 2 ^ 64
    /\ Forall (mfact_ok segs L CS E (write_to_mem m (wa (zden E a)) (cbytes (cden E c)))) tgt
    /\ (forall f, In f rest -> In f mf).
  Proof.
    intros chunks pf mf a w c tgt rest HP HM OKW SZ WF.
    revert tgt rest. induction mf as [|f mf IH]; intros tgt rest H; [discriminate|].
    inversion HM as [|f' mf' Hf HM']; subst f' mf'.
    cbn [store_target_pass] in H.
    assert (SKIP : match store_target_pass chunks pf mf a w c with
                   | Some (t, r) => Some (t, f :: r)
                   | None => None
                   end = Some (tgt, rest) ->
                   store_ok segs m (wa (zden E a)) (N.to_nat w) = true
                   /\ 0 <= zden E a /\ zden E a + Z.of_N w <= 2 ^ 64
                   /\ Forall (mfact_ok segs L CS E (write_to_mem m (wa (zden E a)) (cbytes (cden E c)))) tgt
                   /\ (forall g, In g rest -> In g (f :: mf))).
    { intros HS. destruct (store_target_pass chunks pf mf a w c) as [[t r]|] eqn:ST; [|discriminate].
      injection HS; intros <- <-. destruct (IH HM' t r eq_refl) as (S1 & S2 & S3 & S4 & S5).
      repeat split; try assumption. intros g [<-|Hg]; [left; reflexivity| right; apply S5; exact Hg]. }
    destruct (Bool.eqb chunks _); [|exact (SKIP H)].
    destruct (store_hit pf a w c f) as [[t|]|] eqn:HIT; [|discriminate| exact (SKIP H)].
    injection H; intros <- <-. clear SKIP IH.
    destruct (store_hit_sound pf a w c f t HP Hf OKW SZ WF HIT) as (S1 & S2 & S3 & S4).
    repeat split; try assumption. intros g Hg. right. exact Hg.
  Qed.

  Lemma store_target_sound : forall pf mf a w c tgt rest,
    Forall (pfact_ok CS E) pf -> Forall (mfact_ok segs L CS E m) mf ->
    okw w = true -> cellx_size c = w -> cell_wf (cden E c) ->
    store_target pf mf a w c = Some (tgt, rest) ->
    store_ok segs m (wa (zden E a)) (N.to_nat w) = true
    /\ 0 <= zden E a /\ zden E a + Z.of_N w <= 2 ^ 64
    /\ Forall (mfact_ok segs L CS E (write_to_mem m (wa (zden E a)) (cbytes (cden E c)))) tgt
    /\ (forall f, In f rest -> In f mf).
  Proof.
    intros pf mf a w c tgt rest HP HM OKW SZ WF H. unfold store_target in H.
    destruct (store_target_pass true pf mf a w c) as [r|] eqn:P1.
    - injection H; intros ->. exact (store_target_pass_sound true pf mf a w c tgt rest HP HM OKW SZ WF P1).
    - exact (store_target_pass_sound false pf mf a w c tgt rest HP HM OKW SZ WF H).
  Qed.

  Lemma w_add_sound : forall pf W a b, Forall (pfact_ok CS E) pf -> zden E a <= zden E b ->
    sub_fp (wden E W) (wden E (w_add pf W a b)) /\ inside (wden E (w_add pf W a b)) (zden E a) (zden E b - zden E a).
  Proof.
    intros pf W a b HP Hab. unfold wden, sub_fp. induction W as [|[l h] W IH].
    - cbn. rewrite !zdenp_ok. split; [intros; exact I| left; lia].
    - assert (KEEP : (forall x, outside (map (fun lh : expr * expr => (zdenp E (fst lh), zdenp E (snd lh))) ((l, h) :: w_add pf W a b)) x ->
                               outside (map (fun lh : expr * expr => (zdenp E (fst lh), zdenp E (snd lh))) ((l, h) :: W)) x)
                     /\ inside (map (fun lh : expr * expr => (zdenp E (fst lh), zdenp E (snd lh))) ((l, h) :: w_add pf W a b)) (zden E a) (zden E b - zden E a)).
      { destruct IH as [S I]. cbn [map inside outside fst snd]. split; [intros x [H1 H2]; split; [exact H1| apply S; exact H2]| right; exact I]. }
      cbn [w_add].
      destruct (dec_le00 pf l a) eqn:D1; [destruct (dec_le00 pf b h) eqn:D2|]; cbn [andb].
      1: { apply (dec_le00_sound CS E _ _ _ HP) in D1. apply (dec_le00_sound CS E _ _ _ HP) in D2.
           cbn [map inside fst snd]. rewrite !zdenp_ok. split; [intros x Hx; exact Hx| left; lia]. }
      all: destruct (dec_le00 pf l h) eqn:DLH; destruct (expr_eqb b l) eqn:EQ1; destruct (expr_eqb h a) eqn:EQ2; cbn [andb];
        first [ exact KEEP
              | apply expr_eqb_eq in EQ1; subst l; apply (dec_le00_sound CS E _ _ _ HP) in DLH;
                cbn [map inside outside fst snd]; rewrite !zdenp_ok; split; [intros x [H1 H2]; split; [lia| exact H2]| left; lia]
              | apply expr_eqb_eq in EQ2; subst h; apply (dec_le00_sound CS E _ _ _ HP) in DLH;
                cbn [map inside outside fst snd]; rewrite !zdenp_ok; split; [intros x [H1 H2]; split; [lia| exact H2]| left; lia] ].
  Qed.

  (* [comment removed for export] *)
  Lemma csden_app : forall cs ds, csden E (cs ++ ds) = csden E cs ++ csden E ds.
  Proof. intros. unfold csden. apply map_app. Qed.

  Lemma take_rw_at_sound : forall mm b mf ds r, take_rw_at b mf = Some (ds, r) ->
    Forall (mfact_ok segs L CS E mm) mf -> rw_cells segs mm (zden E b) (csden E ds) /\ Forall (mfact_ok segs L CS E mm) r.
  Proof.
    intros mm b. induction mf as [|f mf IH]; intros ds r H HF; cbn in H; [discriminate|].
    inversion HF as [|f' mf' Hf HF']; subst f' mf'.
    assert (SKIP : match take_rw_at b mf with Some (ds0, r0) => Some (ds0, f :: r0) | None => None end = Some (ds, r) ->
                   rw_cells segs mm (zden E b) (csden E ds) /\ Forall (mfact_ok segs L CS E mm) r).
    { intros H'. destruct (take_rw_at b mf) as [[ds0 r0]|] eqn:T; [|discriminate]. injection H'; intros <- <-.
      destruct (IH ds0 r0 eq_refl HF') as [A B]. split; [exact A| constructor; assumption]. }
    destruct f as [b' cs|b' cs|b' n k|lo hi|oa on|ok_k ok_l sh_l|ra_ rw_ rl_ rn_ rwr_|mW mi mj|mi mj|ml mX mi mj|ml ma mn|ml ma mn|qbl qok|ql qbl qsp qX qi qj|ql qs qa qn|qa qn qbl|ql qk|qj qo qn qxs qok]; try (apply SKIP; exact H).
    destruct (expr_eqb b b') eqn:EQ; [|apply SKIP; exact H].
    injection H; intros <- <-. apply expr_eqb_eq in EQ. subst b'. cbn in Hf. rewrite zdenp_ok in Hf. split; [exact Hf| exact HF'].
  Qed.

  Lemma take_rw_ending_sound : forall mm a mf b ds r, take_rw_ending a mf = Some (b, ds, r) ->
    Forall (mfact_ok segs L CS E mm) mf ->
    rw_cells segs mm (zden E b) (csden E ds) /\ zden E b + Z.of_nat (cells_size (csden E ds)) = zden E a /\ Forall (mfact_ok segs L CS E mm) r.
  Proof.
    intros mm a. induction mf as [|f mf IH]; intros b ds r H HF; cbn -[eadd expr_eqb cells_sizeN] in H; [discriminate|].
    inversion HF as [|f' mf' Hf HF']; subst f' mf'.
    assert (SKIP : match take_rw_ending a mf with Some (b0, ds0, r0) => Some (b0, ds0, f :: r0) | None => None end = Some (b, ds, r) ->
                   rw_cells segs mm (zden E b) (csden E ds) /\ zden E b + Z.of_nat (cells_size (csden E ds)) = zden E a /\ Forall (mfact_ok segs L CS E mm) r).
    { intros H'. destruct (take_rw_ending a mf) as [[[b0 ds0] r0]|] eqn:T; [|discriminate]. injection H'; intros <- <- <-.
      destruct (IH b0 ds0 r0 eq_refl HF') as (A & B & C0). split; [exact A|]. split; [exact B| constructor; assumption]. }
    destruct f as [b' cs|b' cs|b' n k|lo hi|oa on|ok_k ok_l sh_l|ra_ rw_ rl_ rn_ rwr_|mW mi mj|mi mj|ml mX mi mj|ml ma mn|ml ma mn|qbl qok|ql qbl qsp qX qi qj|ql qs qa qn|qa qn qbl|ql qk|qj qo qn qxs qok]; try (apply SKIP; exact H).
    destruct (expr_eqb (eadd b' (ELit (Z.of_N (cells_sizeN cs)))) a) eqn:EQ; [|apply SKIP; exact H].
    injection H; intros <- <- <-. apply expr_eqb_eq in EQ. cbn in Hf. rewrite zdenp_ok in Hf.
    split; [exact Hf|]. split; [| exact HF'].
    rewrite <- EQ, eadd_den. cbn [zden]. rewrite csden_size. lia.
  Qed.

  Lemma coalesce_sound : forall mm f rest, mfact_ok segs L CS E mm f -> Forall (mfact_ok segs L CS E mm) rest ->
    Forall (mfact_ok segs L CS E mm) (coalesce f rest).
  Proof.
    intros mm f rest Hf HR. unfold coalesce.
    destruct f as [a cs|a cs|a n k|lo hi|oa on|ok_k ok_l sh_l|ra_ rw_ rl_ rn_ rwr_|mW mi mj|mi mj|ml mX mi mj|ml ma mn|ml ma mn|qbl qok|ql qbl qsp qX qi qj|ql qs qa qn|qa qn qbl|ql qk|qj qo qn qxs qok]; try (constructor; assumption).
    cbn in Hf. rewrite zdenp_ok in Hf.
    assert (STEP1 : forall a1 cs1 rest1,
              match take_rw_at (eadd a (ELit (Z.of_N (cells_sizeN cs)))) rest with
              | Some (ds, r) => (a, cs ++ ds, r) | None => (a, cs, rest) end = (a1, cs1, rest1) ->
              rw_cells segs mm (zden E a1) (csden E cs1) /\ Forall (mfact_ok segs L CS E mm) rest1).
    { intros a1 cs1 rest1 H. destruct (take_rw_at _ rest) as [[ds r]|] eqn:T.
      - injection H; intros <- <- <-. destruct (take_rw_at_sound mm _ _ _ _ T HR) as [A B].
        split; [|exact B]. rewrite csden_app. apply (proj2 (rw_cells_app segs mm _ _ _)). split; [exact Hf|].
        rewrite eadd_den in A. cbn [zden] in A. rewrite csden_size. replace (Z.of_nat (N.to_nat (cells_sizeN cs))) with (Z.of_N (cells_sizeN cs)) by lia. exact A.
      - injection H; intros <- <- <-. split; [exact Hf| exact HR]. }
    destruct (match take_rw_at (eadd a (ELit (Z.of_N (cells_sizeN cs)))) rest with
              | Some (ds, r) => (a, cs ++ ds, r) | None => (a, cs, rest) end) as [[a1 cs1] rest1] eqn:S1.
    destruct (STEP1 a1 cs1 rest1 eq_refl) as [H1 HR1].
    destruct (take_rw_ending a1 rest1) as [[[b ds] r]|] eqn:T2.
    - destruct (take_rw_ending_sound mm _ _ _ _ _ T2 HR1) as (A & B & C0).
      constructor; [| exact C0]. cbn. rewrite zdenp_ok, csden_app. apply (proj2 (rw_cells_app segs mm _ _ _)). split; [exact A|]. rewrite B. exact H1.
    - constructor; [| exact HR1]. cbn. rewrite zdenp_ok. exact H1.
  Qed.

  Lemma tidy_sound : forall mm mf, Forall (mfact_ok segs L CS E mm) mf -> Forall (mfact_ok segs L CS E mm) (tidy mf).
  Proof.
    intros mm mf HF. unfold tidy.
    assert (HF' : Forall (mfact_ok segs L CS E mm) (List.filter (fun f => negb (mstk_empty f)) mf)).
    { apply List.Forall_forall. intros f Hin. apply filter_In in Hin as [Hin _]. rewrite List.Forall_forall in HF. apply HF. exact Hin. }
    destruct (List.filter _ mf) as [|f rest]; [constructor|]. inversion HF'; subst. apply coalesce_sound; assumption.
  Qed.

  (* [comment removed for export] *)
  Theorem sym_store_sound : forall cl ss a w v mf' W',
    Forall (mfact_ok segs L CS E m) (s_mf ss) -> Forall (pfact_ok CS E) (s_pf ss) ->
    acls_ok cl (zden E a) (Z.of_N w) -> okw w = true -> mem_inv segs m ->
    sym_store C cl ss a w v = StOk mf' W' ->
    let bs := st_bytes w (rden E v) in
    store_ok segs m (wa (zden E a)) (N.to_nat w) = true
    /\ Forall (mfact_ok segs L CS E (write_to_mem m (wa (zden E a)) bs)) mf'
    /\ (sub_fp (wden E (s_W ss)) (wden E W') /\ inside (wden E W') (zden E a) (Z.of_N w))
    /\ length bs = N.to_nat w
    /\ 0 <= zden E a /\ zden E a + Z.of_N w <= 2 ^ 64.
  Proof.
    intros cl ss a w v mf' W' HM HP ACL OKW MI0 H. unfold sym_store in H.
    destruct (store_target (s_pf ss) (s_mf ss) a w (store_cell w v)) as [[tgt rest]|] eqn:ST; [|discriminate].
    injection H; intros <- <-.
    rewrite <- (store_cell_bytes w v OKW).
    destruct (store_target_sound _ _ _ _ _ _ _ HP HM OKW (store_cell_size w v) (store_cell_wf E w v) ST) as (SOK & A0 & A1 & TGT & REST).
    assert (LEN : length (cbytes (cden E (store_cell w v))) = N.to_nat w).
    { rewrite cbytes_length, cden_size, store_cell_size by apply store_cell_wf. reflexivity. }
    split; [exact SOK|].
    split; [| split; [| split; [exact LEN| split; [exact A0| exact A1]]]].
    2:{ destruct (w_add_sound (s_pf ss) (s_W ss) a (eadd a (ELit (Z.of_N w))) HP ltac:(rewrite eadd_den; cbn [zden]; lia)) as [S I]. split; [exact S|].
        rewrite eadd_den in I. cbn [zden] in I. replace (zden E a + Z.of_N w - zden E a) with (Z.of_N w) in I by lia. exact I. }
    apply tidy_sound.
    apply Forall_app. split; [exact TGT|].
    apply List.Forall_forall. intros f Hf. apply filter_In in Hf as [Hin Hs].
    apply (mf_survives_sound (s_pf ss) (cranges (s_pf ss) (s_mf ss)) (s_mf ss) cl a w f _ HP (cranges_sound _ _ HP HM) HM ACL OKW LEN A0 A1
             ltac:(apply mem_inv_store; [exact MI0| rewrite LEN; exact SOK]) Hs).
    rewrite List.Forall_forall in HM. apply HM. apply REST. exact Hin.
  Qed.
End StoreSound.

End LXH.
