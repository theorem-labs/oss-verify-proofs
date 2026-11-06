(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From Stdlib Require Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Import PropExec AxSyioe AxSyclu Asanz3l.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Booteo9.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Bootha0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Booteo9 Bootx2q Bootha0.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Booteo9.Bootf6d OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bootha0.Boott1m OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Booteo9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bootx2q OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bootha0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.

Module Bootbrx.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From Stdlib Require Import PrimString PrimInt63.
From Stdlib Require Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require PropExec AxSyioe AxSyclu Asanz3l Boot1pr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require PropExec.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AxSyioe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AxSyclu OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanz3l OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Boot1pr OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PropExec.Bootcsk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)

Module BFXI.
Import AX2.
Local Notation "'φ' x" := (Uint63.to_Z x) (at level 0).
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition read4I (chunks : list PrimString.string) (o : int) : option (list byte) :=
  match IMGF.seg_byte_atI chunks o with
  | Some z0 =>
    match IMGF.seg_byte_atI chunks (PrimInt63.add o 1%uint63) with
    | Some z1 =>
      match IMGF.seg_byte_atI chunks (PrimInt63.add o 2%uint63) with
      | Some z2 =>
        match IMGF.seg_byte_atI chunks (PrimInt63.add o 3%uint63) with
        | Some z3 => Some [BFXD.Z_to_bv_f 8 z0; BFXD.Z_to_bv_f 8 z1; BFXD.Z_to_bv_f 8 z2; BFXD.Z_to_bv_f 8 z3]
        | None => None
        end
      | None => None
      end
    | None => None
    end
  | None => None
  end.

Lemma add_small : forall o k off, φ o = Z.of_N off -> Z.of_N off + 4 < 2 ^ 62 -> 0 <= φ k <= 3 ->
  φ (PrimInt63.add o k) = Z.of_N (off + Z.to_N (φ k)).
Proof.
  intros o k off Ho Hoff Hk. rewrite Uint63.add_spec, IMGF.wB63, Ho. rewrite Z.mod_small by lia. lia.
Qed.

Lemma read4I_eq : forall chunks o off, φ o = Z.of_N off -> Z.of_N off + 4 < 2 ^ 62 ->
  read4I chunks o = segment_read_bytes chunks off 4.
Proof.
  intros chunks o off Ho Hoff. unfold read4I. rewrite BFXD.Z_to_bv_f_fe. cbn [segment_read_bytes].
  assert (E1 : φ (PrimInt63.add o 1%uint63) = Z.of_N (off + 1)) by (rewrite (add_small o 1%uint63 off Ho Hoff); [reflexivity|change (φ 1%uint63) with 1; lia]).
  assert (E2 : φ (PrimInt63.add o 2%uint63) = Z.of_N (off + 1 + 1)) by (rewrite (add_small o 2%uint63 off Ho Hoff); [change (φ 2%uint63) with 2; f_equal; lia|change (φ 2%uint63) with 2; lia]).
  assert (E3 : φ (PrimInt63.add o 3%uint63) = Z.of_N (off + 1 + 1 + 1)) by (rewrite (add_small o 3%uint63 off Ho Hoff); [change (φ 3%uint63) with 3; f_equal; lia|change (φ 3%uint63) with 3; lia]).
  rewrite (IMGF.seg_byte_atI_spec chunks o off Ho) by lia.
  rewrite (IMGF.seg_byte_atI_spec chunks _ _ E1) by lia.
  rewrite (IMGF.seg_byte_atI_spec chunks _ _ E2) by lia.
  rewrite (IMGF.seg_byte_atI_spec chunks _ _ E3) by lia.
  destruct (segment_byte_at chunks off) as [b0|]; cbn [option_map]; [|reflexivity].
  destruct (segment_byte_at chunks (off + 1)) as [b1|]; cbn [option_map]; [|reflexivity].
  destruct (segment_byte_at chunks (off + 1 + 1)) as [b2|]; cbn [option_map]; [|reflexivity].
  destruct (segment_byte_at chunks (off + 1 + 1 + 1)) as [b3|]; cbn [option_map]; [|reflexivity].
  rewrite !Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* [comment removed for export] *)
Definition fetch_word_f (segs : list Segment) (addr : word) : option (bv 32) :=
  let a := bv_unsigned addr in
  if Z.odd a then None
  else
    match find_segment segs a 4 with
    | Some seg =>
        if (seg_executable seg && negb (seg_writable seg))%bool then
          match IMGF.z61 (a - Z.of_N (seg_base seg)) with
          | Some o =>
              match read4I (seg_bytes seg) o with
              | Some (b0 :: b1 :: b2 :: b3 :: []) => Some (BFXD.le4_f b3 b2 b1 b0)
              | _ => None
              end
          | None => fetch_word segs addr
          end
        else None
    | None => None
    end.

Lemma fetch_word_f_eq : forall segs addr, fetch_word_f segs addr = fetch_word segs addr.
Proof.
  intros segs addr. unfold fetch_word_f. cbv zeta. rewrite BFXD.le4_f_fe.
  replace (Z.odd (bv_unsigned addr)) with (negb (Z.eqb (bv_unsigned addr mod 2) 0))
    by (rewrite Zmod_odd; destruct (Z.odd (bv_unsigned addr)); reflexivity).
  destruct (negb (Z.eqb (bv_unsigned addr mod 2) 0)) eqn:Hal.
  - unfold fetch_word. rewrite Hal. reflexivity.
  - destruct (find_segment segs (bv_unsigned addr) 4) as [seg|] eqn:Hf.
    + destruct (seg_executable seg && negb (seg_writable seg))%bool eqn:Hg.
      * destruct (IMGF.z61 (bv_unsigned addr - Z.of_N (seg_base seg))) as [o|] eqn:Hz; [|reflexivity].
        apply IMGF.z61_spec in Hz. destruct Hz as [Ho Hr].
        unfold fetch_word. rewrite Hal. unfold code_read. change (Z.of_N 4) with 4. rewrite Hf, Hg.
        rewrite (read4I_eq (seg_bytes seg) o (Z.to_N (bv_unsigned addr - Z.of_N (seg_base seg)))) by (rewrite Z2N.id by lia; lia).
        reflexivity.
      * unfold fetch_word. rewrite Hal. unfold code_read. change (Z.of_N 4) with 4. rewrite Hf, Hg. reflexivity.
    + unfold fetch_word. rewrite Hal. unfold code_read. change (Z.of_N 4) with 4. rewrite Hf. reflexivity.
Qed.
Lemma fetch_word_f_fe : fetch_word_f = fetch_word.
Proof. apply functional_extensionality; intros segs. apply functional_extensionality; intros a. apply fetch_word_f_eq. Qed.

(* [comment removed for export] *)
Definition itab_entry_g :=
  ltac:(let t := eval cbv delta [AX2.itab_entry] in @AX2.itab_entry in
        let t1 := eval pattern (@fetch_word), (@is_ecall), (@decode_any), (@Z_to_bv) in t in
        lazymatch t1 with ?G _ _ _ _ => exact G end).
Definition itab_entry_f := itab_entry_g fetch_word_f BFXD.is_ecall_f BFXD.decode_any_f BFXD.Z_to_bv_f.
Lemma itab_entry_f_fe : itab_entry_f = @AX2.itab_entry.
Proof. unfold itab_entry_f. rewrite fetch_word_f_fe, BFXD.is_ecall_f_fe, BFXD.decode_any_f_fe, BFXD.Z_to_bv_f_fe. reflexivity. Qed.

Definition mk_itab_fuel_g :=
  ltac:(let t := eval cbv delta [AX2.mk_itab_fuel] in @AX2.mk_itab_fuel in
        let t1 := eval pattern (@AX2.itab_entry) in t in
        lazymatch t1 with ?G _ => exact G end).
Definition mk_itab_fuel_f := mk_itab_fuel_g itab_entry_f.
Lemma mk_itab_fuel_f_fe : mk_itab_fuel_f = @AX2.mk_itab_fuel.
Proof. unfold mk_itab_fuel_f. rewrite itab_entry_f_fe. reflexivity. Qed.

Definition mk_itab_ranges_acc_g :=
  ltac:(let t := eval cbv delta [APC.mk_itab_ranges_acc] in @APC.mk_itab_ranges_acc in
        let t1 := eval pattern (@AX2.mk_itab_fuel) in t in
        lazymatch t1 with ?G _ => exact G end).
Definition mk_itab_ranges_acc_f := mk_itab_ranges_acc_g mk_itab_fuel_f.
Lemma mk_itab_ranges_acc_f_fe : mk_itab_ranges_acc_f = @APC.mk_itab_ranges_acc.
Proof. unfold mk_itab_ranges_acc_f. rewrite mk_itab_fuel_f_fe. reflexivity. Qed.

Definition mk_itab_ranges_g :=
  ltac:(let t := eval cbv delta [APC.mk_itab_ranges] in @APC.mk_itab_ranges in
        let t1 := eval pattern (@APC.mk_itab_ranges_acc) in t in
        lazymatch t1 with ?G _ => exact G end).
Definition mk_itab_ranges_f := mk_itab_ranges_g mk_itab_ranges_acc_f.
Lemma mk_itab_ranges_f_fe : mk_itab_ranges_f = @APC.mk_itab_ranges.
Proof. unfold mk_itab_ranges_f. rewrite mk_itab_ranges_acc_f_fe. reflexivity. Qed.
End BFXI.
End Bootbrx.

   (* [comment removed for export] *)
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope Z_scope.

Module CAR2.
Import AX2. Import AX2B. Import BFXP. Import CARF.
Local Notation toZ := Uint63Axioms.to_Z.
Ltac fe := repeat (apply functional_extensionality; intros ?).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition win : Type := (PrimInt63.int * PrimInt63.int)%type.
Fixpoint win_in (W : list win) (a e : PrimInt63.int) : bool :=
  match W with
  | [] => false
  | (lo, hi) :: r => if PrimInt63.leb lo a then (if PrimInt63.leb e hi then true else win_in r a e) else win_in r a e
  end.
Lemma win_in_ex : forall W a e, win_in W a e = true -> exists lo hi, In (lo, hi) W /\ toZ lo <= toZ a /\ toZ e <= toZ hi.
Proof.
  induction W as [|[lo hi] r IH]; intros a e H; [discriminate|]. cbn [win_in] in H.
  destruct (PrimInt63.leb lo a) eqn:E1.
  - destruct (PrimInt63.leb e hi) eqn:E2.
    + exists lo, hi. split; [left; reflexivity|]. split; [exact (ileb_le _ _ E1)|exact (ileb_le _ _ E2)].
    + destruct (IH _ _ H) as (lo' & hi' & HI & HL). exists lo', hi'. split; [right; exact HI|exact HL].
  - destruct (IH _ _ H) as (lo' & hi' & HI & HL). exists lo', hi'. split; [right; exact HI|exact HL].
Qed.

(* [comment removed for export] *)
Definition side_win (bc : bctx) (cm : saddr * expr) : option win :=
  match xloB bc (snd cm) with
  | Some ml => match z2b (a_off (fst cm)) with
               | Some lo => match z2b (a_off (fst cm) + ml) with Some hi => Some (lo, hi) | None => None end
               | None => None
               end
  | None => None
  end.
Fixpoint swin (bc : bctx) (b : expr) (D : list (saddr * expr)) : list win :=
  match D with
  | [] => []
  | cm :: r => if expr_eqbF b (a_base (fst cm)) then match side_win bc cm with Some w => w :: swin bc b r | None => swin bc b r end
               else swin bc b r
  end.
Definition WIN_OK (bc : bctx) (D : list (saddr * expr)) (b : expr) (w : win) : Prop :=
  exists c m ml, In (c, m) D /\ a_base c = b /\ xloB bc m = Some ml /\ toZ (fst w) = a_off c + 2 ^ 59 /\ toZ (snd w) = a_off c + ml + 2 ^ 59.
Lemma WIN_OK_cons : forall bc D x b w, WIN_OK bc D b w -> WIN_OK bc (x :: D) b w.
Proof. intros bc D x b w (c & m & ml & HI & H). exists c, m, ml. split; [right; exact HI|exact H]. Qed.
Lemma side_win_ok : forall bc c m w, side_win bc (c, m) = Some w -> forall D, WIN_OK bc ((c, m) :: D) (a_base c) w.
Proof.
  intros bc c m w H D. unfold side_win in H. cbn [fst snd] in H.
  destruct (xloB bc m) as [ml|] eqn:EX; [|discriminate].
  destruct (z2b (a_off c)) as [lo|] eqn:E1; [|discriminate]. destruct (z2b (a_off c + ml)) as [hi|] eqn:E2; [|discriminate].
  injection H as <-. apply z2b_val in E1. apply z2b_val in E2.
  exists c, m, ml. split; [left; reflexivity|]. split; [reflexivity|]. split; [exact EX|]. cbn [fst snd]. split; [apply E1|apply E2].
Qed.
Lemma swin_ok : forall bc b D w, In w (swin bc b D) -> WIN_OK bc D b w.
Proof.
  intros bc b D. induction D as [|[c m] r IH]; intros w H; [destruct H|]. cbn [swin fst] in H.
  destruct (expr_eqbF b (a_base c)) eqn:EB; [|apply WIN_OK_cons; exact (IH w H)].
  rewrite BLKF.expr_eqbF_eq in EB. apply p_expr_eqb_eq in EB.
  destruct (side_win bc (c, m)) as [w0|] eqn:ES; [|apply WIN_OK_cons; exact (IH w H)].
  destruct H as [<-|H]; [|apply WIN_OK_cons; exact (IH w H)]. rewrite EB. exact (side_win_ok bc c m w0 ES r).
Qed.
Lemma in_sides_num_intro : forall bc D b k n c m, In (c, m) D -> num_sub bc b k n c m = true -> in_sides_num bc D b k n = true.
Proof.
  intros bc D b k n c m. induction D as [|[c0 m0] r IH]; intros HI HN; [destruct HI|]. cbn [in_sides_num].
  destruct HI as [E|HI]; [injection E as -> ->; rewrite HN; reflexivity|].
  destruct (num_sub bc b k n c0 m0); [reflexivity|exact (IH HI HN)].
Qed.
Lemma swin_sound : forall bc D b a e k n, win_in (swin bc b D) a e = true ->
  toZ a = k + 2 ^ 59 -> toZ e = k + n + 2 ^ 59 -> in_sides_num bc D b k n = true.
Proof.
  intros bc D b a e k n H Ha He. destruct (win_in_ex _ _ _ H) as (lo & hi & HI & L1 & L2).
  destruct (swin_ok bc b D (lo, hi) HI) as (c & m & ml & HD & HB & HX & V1 & V2). cbn [fst snd] in V1, V2.
  apply (in_sides_num_intro bc D b k n c m HD). unfold num_sub. rewrite HB, p_expr_eqb_refl, HX.
  destruct (Z.leb_spec (a_off c) k); [|lia]. apply Z.leb_le. lia.
Qed.
(* [comment removed for export] *)
Fixpoint canon_get (cn : list (positive * expr)) (b : positive) : option expr :=
  match cn with [] => None | (b', e) :: r => if Pos.eqb b b' then Some e else canon_get r b end.
Fixpoint mk_canon (sbl : list sbe) : list (positive * expr) :=
  match sbl with
  | [] => []
  | e :: r => match sbe_fl e with (si, _) :: _ => (sbe_b e, a_base (sx_a (si_sx si))) :: mk_canon r | [] => mk_canon r end
  end.
Definition all_canon (cn : list (positive * expr)) (sis : list sxi) : bool :=
  forallbF (fun t => match canon_get cn (sx_bid (si_sx t)) with Some b => expr_eqbF (a_base (sx_a (si_sx t))) b | None => false end) sis.
Fixpoint mk_tbi (bc : bctx) (cn : list (positive * expr)) (D : list (saddr * expr)) : list (positive * list win) :=
  match cn with [] => [] | (b, e) :: r => (b, swin bc e D) :: mk_tbi bc r D end.
Fixpoint tbi_get (tb : list (positive * list win)) (b : positive) : list win :=
  match tb with [] => [] | (b', W) :: r => if Pos.eqb b b' then W else tbi_get r b end.
Lemma tbi_get_mk : forall bc cn D b, tbi_get (mk_tbi bc cn D) b = match canon_get cn b with Some e => swin bc e D | None => [] end.
Proof.
  intros bc cn D b. induction cn as [|[b' e] r IH]; [reflexivity|]. cbn [mk_tbi tbi_get canon_get].
  destruct (Pos.eqb b b'); [reflexivity|exact IH].
Qed.


(* [comment removed for export] *)
Definition num_subF (bc : bctx) (b : expr) (k n : Z) (c : saddr) (m : expr) : bool :=
  if (if expr_eqbF b (a_base c) then Z.leb (a_off c) k else false) then
    match xloB bc m with Some ml => Z.leb (k + n) (a_off c + ml) | None => false end
  else false.
Fixpoint in_sides_numF (bc : bctx) (D : list (saddr * expr)) (b : expr) (k n : Z) : bool :=
  match D with
  | [] => false
  | (c, m) :: r => if num_subF bc b k n c m then true else in_sides_numF bc r b k n
  end.
Lemma in_sides_numF_eq : forall bc D b k n, in_sides_numF bc D b k n = in_sides_num bc D b k n.
Proof.
  intros bc D b k n. induction D as [|[c m] r IH]; [reflexivity|]. cbn [in_sides_numF in_sides_num].
  unfold num_subF, num_sub. rewrite BLKF.expr_eqbF_eq, IH. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition skipS5I (cn : list (positive * expr)) (bc : bctx) (s : sxi) : sxi -> bool :=
  let tb := mk_tbi bc cn (sp_D (sx_sp (si_sx s))) in
  fun t =>
    if Pos.eqb (sx_bid (si_sx s)) (sx_bid (si_sx t)) then
      match si_iv s with Some (a, e) => nonov t a e | None => false end
    else if ssvJ s t then true
    else if (match si_iv t with Some (a, e) => win_in (tbi_get tb (sx_bid (si_sx t))) a e | None => false end) then true
    else in_sides_numF bc (sp_D (sx_sp (si_sx s))) (a_base (sx_a (si_sx t))) (a_off (sx_a (si_sx t))) (sx_m1 (si_sx t)).
Lemma skipS5I_eq : forall cn bc s X sx, canon_get cn (sx_bid sx) = Some (a_base (sx_a sx)) ->
  skipS5I cn bc s (mk_sxi X sx) = skipS5 bc s (mk_sxi X sx).
Proof.
  intros cn bc s X sx HC. unfold skipS5I, skipS5. cbv zeta. rewrite in_sides_numF_eq.
  destruct (Pos.eqb (sx_bid (si_sx s)) (sx_bid (si_sx (mk_sxi X sx)))); [reflexivity|].
  destruct (ssvJ s (mk_sxi X sx)); [reflexivity|].
  cbn [si_iv si_sx mk_sxi]. rewrite tbi_get_mk, HC.
  destruct (iv_of (a_off (sx_a sx)) (Z.of_nat (sx_w sx))) as [[a e]|] eqn:EIV; [|reflexivity].
  destruct (win_in (swin bc (a_base (sx_a sx)) (sp_D (sx_sp (si_sx s)))) a e) eqn:ET; [|reflexivity].
  symmetry. apply iv_of_val in EIV. destruct EIV as (Va & Ve & Hm).
  apply (swin_sound bc _ _ a e _ _ ET Va). unfold sx_m1. rewrite zlit64_small by lia. exact Ve.
Qed.


(* [comment removed for export] *)
Definition skipS5F (bc : bctx) (s t : sxi) : bool :=
  if Pos.eqb (sx_bid (si_sx s)) (sx_bid (si_sx t)) then
    match si_iv s with Some (a, e) => nonov t a e | None => false end
  else if ssvJ s t then true
  else in_sides_numF bc (sp_D (sx_sp (si_sx s))) (a_base (sx_a (si_sx t))) (a_off (sx_a (si_sx t))) (sx_m1 (si_sx t)).
Lemma skipS5F_eq : forall bc s t, skipS5F bc s t = skipS5 bc s t.
Proof. intros. unfold skipS5F, skipS5. rewrite in_sides_numF_eq. reflexivity. Qed.

(* [comment removed for export] *)
Section Skip.
Variable skip : bctx -> sxi -> sxi -> bool.
Fixpoint stores_partF5_g (bc : bctx) (sis : list sxi) (R : list sbe) : list kentry :=
  match sis with
  | [] => []
  | si :: newer =>
      let sx := si_sx si in
      let b := sx_bid sx in
      let R' := sb_pop R b in
      stores_partF5_g bc newer R' ++
      (let gen := fun _ : unit => chainKFF2 bc (si_bx si) (mk_flG (skip bc si) newer) (KWord (sx_a sx) (sx_w sx) (sx_v sx))
                                    (Some (a_base (sx_a sx))) (Pos.eqb b) (sx_br sx) None in
       match si_iv si, si_eabj si with
       | Some (a, e), Some (el, eh) =>
           if forallbF (fun e' => if Pos.eqb b (sbe_b e') then true else hs_other (sbe_h e') el eh) R'
           then match sb_find R' b with
                | Some se => chainKI bc (si_bx si) (sbe_fl se) a e (KWord (sx_a sx) (sx_w sx) (sx_v sx))
                                     (Some (a_base (sx_a sx))) (Pos.eqb b) (sx_br sx)
                | None => gen tt
                end
           else gen tt
       | _, _ => gen tt
       end)
  end.
Fixpoint sp9_g (bc : bctx) (sbl : list sbe) (sis : list sxi) : list ixb * list kentry :=
  match sis with
  | [] => ([], [])
  | si :: newer =>
      let '(ixs, racc) := sp9_g bc sbl newer in
      let sx := si_sx si in
      let b := sx_bid sx in
      let K := KWord (sx_a sx) (sx_w sx) (sx_v sx) in
      let gen := fun _ : unit => chainKFF2 bc (si_bx si) (mk_flG (skip bc si) newer) K (Some (a_base (sx_a sx))) (Pos.eqb b) (sx_br sx) None in
      let P := match si_iv si, si_eabj si with
               | Some (a, e), Some (el, eh) =>
                   if forallbF (fun e' => if Pos.eqb b (sbe_b e') then true else hs_other (sbe_h e') el eh) sbl
                   then chainKI bc (si_bx si) (match ix_cands ixs b a e with Some fl => fl | None => mk_flG (osame b) newer end) a e K
                                (Some (a_base (sx_a sx))) (Pos.eqb b) (sx_br sx)
                   else gen tt
               | _, _ => gen tt
               end in
      (ix_add ixs si newer, rev_append P racc)
  end.
End Skip.
Definition stores_partX2 (bc : bctx) (sis : list sxi) (sbl : list sbe) : list kentry :=
  if long_log sis then
    let cn := mk_canon sbl in
    if all_canon cn sis then rev' (snd (sp9_g (skipS5I cn) bc sbl sis)) else stores_partF9 bc sis sbl
  else stores_partF5_g skipS5F bc sis sbl.
Lemma mk_flG_ext : forall (f g : sxi -> bool) l, (forall t, In t l -> f t = g t) -> mk_flG f l = mk_flG g l.
Proof.
  intros f g l. induction l as [|t r IH]; intros H; [reflexivity|]. cbn [mk_flG].
  rewrite (H t (or_introl eq_refl)), (IH (fun t' Ht' => H t' (or_intror Ht'))). reflexivity.
Qed.
Definition IMG (cn : list (positive * expr)) (X : ptree (option bx)) (l : list sxi) : Prop :=
  forall t, In t l -> exists sx, t = mk_sxi X sx /\ canon_get cn (sx_bid sx) = Some (a_base (sx_a sx)).
Lemma IMG_tl : forall cn X t l, IMG cn X (t :: l) -> IMG cn X l.
Proof. intros cn X t l H t' Ht'. exact (H t' (or_intror Ht')). Qed.
Lemma flI_eq : forall cn bc X si newer, IMG cn X newer -> mk_flG (skipS5I cn bc si) newer = mk_flG (skipS5 bc si) newer.
Proof. intros cn bc X si newer H. apply mk_flG_ext. intros t Ht. destruct (H t Ht) as (sx & -> & HC). apply skipS5I_eq. exact HC. Qed.
Lemma stores_partF5_g_eq : forall bc sis R, stores_partF5_g skipS5F bc sis R = stores_partF5 bc sis R.
Proof.
  intros bc sis. induction sis as [|si newer IH]; intros R; [reflexivity|].
  cbn [stores_partF5_g stores_partF5]. rewrite IH, (mk_flG_ext (skipS5F bc si) (skipS5 bc si) newer (fun t _ => skipS5F_eq bc si t)). reflexivity.
Qed.
Lemma sp9_g_eq : forall cn bc X sbl sis, IMG cn X sis -> sp9_g (skipS5I cn) bc sbl sis = sp9 bc sbl sis.
Proof.
  intros cn bc X sbl sis. induction sis as [|si newer IH]; intros H; [reflexivity|].
  cbn [sp9_g sp9]. rewrite (IH (IMG_tl _ _ _ _ H)), (flI_eq cn bc X si newer (IMG_tl _ _ _ _ H)). reflexivity.
Qed.
Lemma all_canon_img : forall cn X sxs, all_canon cn (map (mk_sxi X) sxs) = true -> IMG cn X (map (mk_sxi X) sxs).
Proof.
  intros cn X sxs H t Ht. pose proof (forallbF_in _ _ _ H t Ht) as HT. cbv beta in HT.
  apply in_map_iff in Ht. destruct Ht as (sx & <- & _). exists sx. split; [reflexivity|]. cbn [si_sx mk_sxi] in HT.
  destruct (canon_get cn (sx_bid sx)) as [b|]; [|discriminate]. rewrite BLKF.expr_eqbF_eq in HT. apply p_expr_eqb_eq in HT. rewrite HT. reflexivity.
Qed.
Lemma stores_partX2_eq : forall bc X sxs sbl, stores_partX2 bc (map (mk_sxi X) sxs) sbl = stores_partX bc (map (mk_sxi X) sxs) sbl.
Proof.
  intros bc X sxs sbl. unfold stores_partX2, stores_partX. rewrite stores_partF5_g_eq.
  destruct (long_log (map (mk_sxi X) sxs)); [|reflexivity]. cbv zeta.
  destruct (all_canon (mk_canon sbl) (map (mk_sxi X) sxs)) eqn:EC; [|reflexivity].
  unfold stores_partF9. rewrite (sp9_g_eq _ bc X sbl _ (all_canon_img _ X sxs EC)). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition gW (tb : list (positive * list win)) (b : positive) (el eh : PrimInt63.int) (p : positive * option hull) : bool :=
  if Pos.eqb b (fst p) then true
  else if hs_other (snd p) el eh then true
  else match snd p with Some (_, _, c0, d0) => win_in (tbi_get tb (fst p)) c0 d0 | None => false end.
Lemma swin_sound_hull : forall bc D b c0 d0 a e k n, win_in (swin bc b D) c0 d0 = true ->
  toZ c0 <= toZ a -> toZ e <= toZ d0 -> toZ a = k + 2 ^ 59 -> toZ e = k + n + 2 ^ 59 -> in_sides_num bc D b k n = true.
Proof.
  intros bc D b c0 d0 a e k n H L1 L2 Ha He. destruct (win_in_ex _ _ _ H) as (lo & hi & HI & M1 & M2).
  destruct (swin_ok bc b D (lo, hi) HI) as (c & m & ml & HD & HB & HX & V1 & V2). cbn [fst snd] in V1, V2.
  apply (in_sides_num_intro bc D b k n c m HD). unfold num_sub. rewrite HB, p_expr_eqb_refl, HX.
  destruct (Z.leb_spec (a_off c) k); [|lia]. apply Z.leb_le. lia.
Qed.
(* [comment removed for export] *)
Fixpoint stores_partF5w (cn : list (positive * expr)) (bc : bctx) (sis : list sxi) (R : list sbe) : list kentry :=
  match sis with
  | [] => []
  | si :: newer =>
      let sx := si_sx si in
      let b := sx_bid sx in
      let R' := sb_pop R b in
      stores_partF5w cn bc newer R' ++
      (let gen := fun _ : unit => chainKFF2 bc (si_bx si) (mk_flG (skipS5I cn bc si) newer) (KWord (sx_a sx) (sx_w sx) (sx_v sx))
                                    (Some (a_base (sx_a sx))) (Pos.eqb b) (sx_br sx) None in
       match si_iv si, si_eabj si with
       | Some (a, e), Some (el, eh) =>
           if (if forallbF (fun e' => if Pos.eqb b (sbe_b e') then true else hs_other (sbe_h e') el eh) R' then true
               else forallbF (fun e' => gW (mk_tbi bc cn (sp_D (sx_sp sx))) b el eh (sbkey e')) R')
           then match sb_find R' b with
                | Some se => chainKI bc (si_bx si) (sbe_fl se) a e (KWord (sx_a sx) (sx_w sx) (sx_v sx))
                                     (Some (a_base (sx_a sx))) (Pos.eqb b) (sx_br sx)
                | None => gen tt
                end
           else gen tt
       | _, _ => gen tt
       end)
  end.
Fixpoint sp9w (cn : list (positive * expr)) (bc : bctx) (sbl : list sbe) (sis : list sxi) : list ixb * list kentry :=
  match sis with
  | [] => ([], [])
  | si :: newer =>
      let '(ixs, racc) := sp9w cn bc sbl newer in
      let sx := si_sx si in
      let b := sx_bid sx in
      let K := KWord (sx_a sx) (sx_w sx) (sx_v sx) in
      let gen := fun _ : unit => chainKFF2 bc (si_bx si) (mk_flG (skipS5I cn bc si) newer) K (Some (a_base (sx_a sx))) (Pos.eqb b) (sx_br sx) None in
      let P := match si_iv si, si_eabj si with
               | Some (a, e), Some (el, eh) =>
                   if (if forallbF (fun e' => if Pos.eqb b (sbe_b e') then true else hs_other (sbe_h e') el eh) sbl then true
                       else forallbF (fun e' => gW (mk_tbi bc cn (sp_D (sx_sp sx))) b el eh (sbkey e')) sbl)
                   then chainKI bc (si_bx si) (match ix_cands ixs b a e with Some fl => fl | None => mk_flG (osame b) newer end) a e K
                                (Some (a_base (sx_a sx))) (Pos.eqb b) (sx_br sx)
                   else gen tt
               | _, _ => gen tt
               end in
      (ix_add ixs si newer, rev_append P racc)
  end.
Lemma sp9w_eq : forall cn bc all sbl sis R,
  SBL_OK all sis R -> (forall si, In si sis -> exists e, In e R /\ sbe_b e = sx_bid (si_sx si)) -> map sbkey R = map sbkey sbl ->
  IXL_OK sis (fst (sp9w cn bc sbl sis)) /\ rev (snd (sp9w cn bc sbl sis)) = stores_partF5w cn bc sis R.
Proof.
  intros cn bc all sbl sis. induction sis as [|si newer IH]; intros R HR HC HK.
  - cbn [sp9w fst snd stores_partF5w rev]. split; [|reflexivity]. split; [intros b x H; discriminate H|intros b _; reflexivity].
  - cbn [sp9w stores_partF5w]. cbv zeta.
    set (b := sx_bid (si_sx si)).
    assert (HR' : SBL_OK all newer (sb_pop R b)) by (apply sb_pop_ok; exact HR).
    assert (HC' : forall si', In si' newer -> exists e, In e (sb_pop R b) /\ sbe_b e = sx_bid (si_sx si')).
    { intros si' Hsi. destruct (HC si' (or_intror Hsi)) as (e0 & He0 & Hb0).
      destruct (sb_pop_bases R b e0 He0) as (e & E1 & E2 & _). exists e. split; [exact E1|congruence]. }
    assert (HK' : map sbkey (sb_pop R b) = map sbkey sbl) by (rewrite sb_pop_keys; exact HK).
    destruct (IH _ HR' HC' HK') as [HIX HREV].
    destruct (sp9w cn bc sbl newer) as [ixs racc] eqn:ESP. cbn [fst snd] in *.
    split; [apply IXL_OK_add; exact HIX|].
    rewrite rev_append_rev, rev_app_distr, rev_involutive, HREV. f_equal.
    destruct (si_iv si) as [[a e]|] eqn:EIV; [|reflexivity].
    destruct (si_eabj si) as [[el eh]|] eqn:EE; [|reflexivity].
    rewrite (forallbF_hs b el eh (sb_pop R b) sbl HK').
    rewrite (forallbF_keys (gW (mk_tbi bc cn (sp_D (sx_sp (si_sx si)))) b el eh) (sb_pop R b) sbl HK').
    destruct (if forallbF _ sbl then true else forallbF _ sbl); [|reflexivity].
    destruct (sb_find_some (sb_pop R b) b) as [se ESB].
    { destruct (HC si (or_introl eq_refl)) as (e0 & He0 & Hb0). destruct (sb_pop_bases R b e0 He0) as (e1 & E1 & E2 & _).
      exists e1. split; [exact E1|]. rewrite E2. exact Hb0. }
    rewrite ESB. destruct (sb_find_in _ _ _ ESB) as [Hse Hseb]. destruct (HR' se Hse) as [_ HFL]. rewrite HFL, Hseb.
    destruct (ix_cands ixs b a e) as [fl|] eqn:EC; [|reflexivity].
    apply (ix_cands_ok newer ixs b a e fl HIX EC).
Qed.
Lemma stores_partF5w_eq : forall cn bc X tt all sxs R, XOK bc X -> Forall (SX_OK bc tt) sxs ->
  SBL_OK all (map (mk_sxi X) sxs) R ->
  (forall si, In si (map (mk_sxi X) sxs) -> exists e, In e R /\ sbe_b e = sx_bid (si_sx si)) ->
  (forall si, In si (map (mk_sxi X) sxs) -> In si all) ->
  IMG cn X all ->
  stores_partF5w cn bc (map (mk_sxi X) sxs) R = stores_part bc sxs.
Proof.
  intros cn bc X tt all sxs. induction sxs as [|sx rest IH]; intros R HX HSX HR HC HI HIMG; [reflexivity|].
  pose proof (Forall_inv HSX) as HSX0. pose proof (Forall_inv_tail HSX) as HSXr.
  cbn [map stores_partF5w stores_part]. cbv zeta.
  assert (HR' : SBL_OK all (map (mk_sxi X) rest) (sb_pop R (sx_bid (si_sx (mk_sxi X sx))))) by (apply sb_pop_ok; exact HR).
  assert (HC' : forall si, In si (map (mk_sxi X) rest) -> exists e, In e (sb_pop R (sx_bid (si_sx (mk_sxi X sx)))) /\ sbe_b e = sx_bid (si_sx si)).
  { intros si Hsi. destruct (HC si (or_intror Hsi)) as (e0 & He0 & Hb0).
    destruct (sb_pop_bases R (sx_bid (si_sx (mk_sxi X sx))) e0 He0) as (e & H1 & H2 & _). exists e. split; [exact H1|congruence]. }
  rewrite (IH _ HX HSXr HR' HC' (fun si Hsi => HI si (or_intror Hsi)) HIMG). f_equal.
  cbn [si_sx si_bx si_iv si_eabj mk_sxi].
  assert (IMGr : IMG cn X (map (mk_sxi X) rest)) by (intros t0 Ht0; apply HIMG; apply HI; right; exact Ht0).
  rewrite (flI_eq cn bc X (mk_sxi X sx) (map (mk_sxi X) rest) IMGr).
  assert (GEN : chainKFF2 bc (xget X (sx_bid sx)) (mk_flG (skipS5 bc (mk_sxi X sx)) (map (mk_sxi X) rest)) (KWord (sx_a sx) (sx_w sx) (sx_v sx))
                  (Some (a_base (sx_a sx))) (Pos.eqb (sx_bid sx)) (sx_br sx) None
                = chainK2 bc rest (KWord (sx_a sx) (sx_w sx) (sx_v sx)) (Some (a_base (sx_a sx))) (Pos.eqb (sx_bid sx)) (sx_br sx)).
  { apply (chainKFF2_eqG2 bc X); [exact HX|apply HX| |exact I|].
    - destruct (sx_a sx); reflexivity.
    - intros t Hin Ht. unfold skipS5 in Ht. cbn [si_sx si_iv mk_sxi] in Ht.
      destruct (Pos.eqb (sx_bid sx) (sx_bid t)) eqn:ES.
      + destruct (iv_of (a_off (sx_a sx)) (Z.of_nat (sx_w sx))) as [[a e]|] eqn:EIV; [|discriminate].
        apply (nonov_keep bc X t _ a e _ _); [|exact Ht|].
        * destruct (sx_a sx) as [kb kk]. exact EIV.
        * destruct (sx_a sx) as [kb kk]. reflexivity.
      + left. symmetry. destruct (ssvJ (mk_sxi X sx) (mk_sxi X t)) eqn:EJ; [exact (ssvJ_keep bc X sx t EJ ES)|].
        exact (sym_keep bc sx t (proj2 (proj2 HSX0)) (proj2 (proj2 (proj1 (Forall_forall _ _) HSXr t Hin))) Ht). }
  destruct (iv_of (a_off (sx_a sx)) (Z.of_nat (sx_w sx))) as [[a e]|] eqn:EIV; [|exact GEN].
  destruct (if obr_eqb (sx_br sx) (sp_rng (sx_sp sx))
            then match mk_abj (sp_rng (sx_sp sx)) (Some (a, e)) with Some (A, B) => Some (B, A) | None => None end else None) as [[el eh]|] eqn:EE; [|exact GEN].
  destruct (if forallbF (fun e' => if Pos.eqb (sx_bid sx) (sbe_b e') then true else hs_other (sbe_h e') el eh) (sb_pop R (sx_bid sx)) then true
            else forallbF (fun e' => gW (mk_tbi bc cn (sp_D (sx_sp sx))) (sx_bid sx) el eh (sbkey e')) (sb_pop R (sx_bid sx))) eqn:EALL; [|exact GEN].
  destruct (sb_find (sb_pop R (sx_bid sx)) (sx_bid sx)) as [se|] eqn:ESB; [|exact GEN].
  destruct (sb_find_in _ _ _ ESB) as [Hse Hseb]. destruct (HR' se Hse) as [_ HFL]. cbn [si_sx mk_sxi] in HFL. rewrite Hseb in HFL.
  rewrite HFL, chainKI_eq.
  apply (chainKFF2_eqG2 bc X); [exact HX|apply HX| |exact I|].
  - destruct (sx_a sx); reflexivity.
  - intros t Ht HSK. unfold osame in HSK. cbn [si_sx mk_sxi] in HSK.
    destruct (Pos.eqb (sx_bid sx) (sx_bid t)) eqn:ES.
    + apply (nonov_keep bc X t _ a e _ _); [|exact HSK|].
      * destruct (sx_a sx) as [kb kk]. exact EIV.
      * destruct (sx_a sx) as [kb kk]. reflexivity.
    + left. symmetry.
      destruct (HC' (mk_sxi X t) (in_map _ _ _ Ht)) as (e' & He' & Hb'). cbn [si_sx mk_sxi] in Hb'.
      destruct (HR' e' He') as [HOK _]. unfold SBE_OK in HOK. rewrite Hb' in HOK.
      destruct (mk_flG_in (osame (sx_bid t)) all (mk_sxi X t) (HI _ (or_intror (in_map _ _ _ Ht)))) as [r Hr].
      { unfold osame. cbn [si_sx mk_sxi]. rewrite Pos.eqb_refl. reflexivity. }
      assert (HV : hs_other (sbe_h e') el eh = true \/
                   exists A0 B0 c0 d0, sbe_h e' = Some (A0, B0, c0, d0) /\ win_in (tbi_get (mk_tbi bc cn (sp_D (sx_sp sx))) (sx_bid t)) c0 d0 = true).
      { destruct (forallbF (fun e' => if Pos.eqb (sx_bid sx) (sbe_b e') then true else hs_other (sbe_h e') el eh) (sb_pop R (sx_bid sx))) eqn:EOLD.
        - left. pose proof (forallbF_in _ _ _ EOLD e' He') as HV0. cbv beta in HV0. rewrite Hb', ES in HV0. exact HV0.
        - pose proof (forallbF_in _ _ _ EALL e' He') as HV0. cbv beta in HV0. unfold gW, sbkey in HV0. cbn [fst snd] in HV0. rewrite Hb', ES in HV0.
          destruct (hs_other (sbe_h e') el eh); [left; reflexivity|]. right.
          destruct (sbe_h e') as [[[[A0 B0] c0] d0]|]; [|discriminate]. exists A0, B0, c0, d0. split; [reflexivity|exact HV0]. }
      destruct HV as [HV|(A0 & B0 & c0 & d0 & EH0 & HW)].
      * (* [comment removed for export] *)
        apply (ssvJ_keep bc X sx t); [|exact ES].
        rewrite HOK in HV. unfold hs_other in HV.
        destruct (hull_of (mk_flG (osame (sx_bid t)) all)) as [[[[A1 B1] c1] d1]|] eqn:EH; [|discriminate].
        destruct (hull_of_cov _ _ _ _ _ EH _ _ Hr) as (A & B & c & d & EA & _ & LA & LB & _ & _).
        unfold ssvJ. rewrite EA. cbn [si_eabj mk_sxi]. rewrite EIV, EE.
        destruct (PrimInt63.leb A1 el) eqn:L.
        -- apply ileb_le in L. rewrite (ileb_true A el) by lia. reflexivity.
        -- apply ileb_le in HV. destruct (PrimInt63.leb A el); [reflexivity|]. apply ileb_true. lia.
      * (* [comment removed for export] *)
        rewrite HOK in EH0.
        destruct (hull_of_cov _ _ _ _ _ EH0 _ _ Hr) as (A & B & c & d & _ & EIVt & _ & _ & Lc & Ld).
        cbn [si_iv mk_sxi] in EIVt.
        destruct (HIMG (mk_sxi X t) (HI _ (or_intror (in_map _ _ _ Ht)))) as (sx' & Esx & HCt).
        assert (Et : sx' = t) by (apply (f_equal si_sx) in Esx; cbn [si_sx mk_sxi] in Esx; symmetry; exact Esx). subst sx'.
        rewrite tbi_get_mk, HCt in HW.
        destruct (iv_of_val _ _ _ _ EIVt) as (Va & Ve & Hm).
        apply (sym_keep bc sx t (proj2 (proj2 HSX0)) (proj2 (proj2 (proj1 (Forall_forall _ _) HSXr t Ht)))).
        unfold sx_m1. rewrite zlit64_small by lia.
        exact (swin_sound_hull bc _ _ c0 d0 c d _ _ HW Lc Ld Va Ve).
Qed.
Definition stores_partX3 (bc : bctx) (sis : list sxi) (sbl : list sbe) : list kentry :=
  if long_log sis then
    let cn := mk_canon sbl in
    if all_canon cn sis then rev' (snd (sp9w cn bc sbl sis)) else stores_partF9 bc sis sbl
  else stores_partF5_g skipS5F bc sis sbl.
Lemma stores_partX3_eq : forall bc X tt sxs, XOK bc X -> Forall (SX_OK bc tt) sxs ->
  stores_partX3 bc (map (mk_sxi X) sxs) (mk_sbl (map (mk_sxi X) sxs) (map (mk_sxi X) sxs) []) = stores_part bc sxs.
Proof.
  intros bc X tt sxs HX HS. set (sis := map (mk_sxi X) sxs).
  destruct (mk_sbl_ok sis sis [] (fun e (H : In e []) => match H with end)) as (HSB1 & HSB2 & _).
  unfold stores_partX3. destruct (long_log sis).
  - cbv zeta. destruct (all_canon (mk_canon (mk_sbl sis sis [])) sis) eqn:EC.
    + unfold rev'. rewrite <- rev_alt. rewrite (proj2 (sp9w_eq _ bc sis _ sis _ HSB1 HSB2 eq_refl)).
      apply (stores_partF5w_eq _ bc X tt sis sxs _ HX HS HSB1 HSB2 (fun si H => H)). exact (all_canon_img _ X sxs EC).
    + rewrite (stores_partF9_eq bc sis sis _ HSB1 HSB2). exact (stores_partF5_eq bc X tt sis sxs _ HX HS HSB1 HSB2 (fun si H => H)).
  - rewrite stores_partF5_g_eq. exact (stores_partF5_eq bc X tt sis sxs _ HX HS HSB1 HSB2 (fun si H => H)).
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition side_lwin (bc : bctx) (cm : saddr * expr) : option win :=
  match a_base (fst cm) with
  | ELit zs =>
      match xloB bc (snd cm) with
      | Some ml => let lo := zlit64 zs + a_off (fst cm) in
                   match z2b lo with
                   | Some l => match z2b (lo + ml) with Some h => Some (l, h) | None => None end
                   | None => None
                   end
      | None => None
      end
  | _ => None
  end.
Fixpoint mk_lw (bc : bctx) (D : list (saddr * expr)) : list win :=
  match D with
  | [] => []
  | cm :: r => match side_lwin bc cm with Some w => w :: mk_lw bc r | None => mk_lw bc r end
  end.
Definition lw_of (bc : bctx) (p : sxi * list sxi) : list win := mk_lw bc (sp_D (sx_sp (si_sx (fst p)))).
Definition LWIN_OK (bc : bctx) (D : list (saddr * expr)) (w : win) : Prop :=
  exists c m zs ml, In (c, m) D /\ a_base c = ELit zs /\ xloB bc m = Some ml /\
    toZ (fst w) = zlit64 zs + a_off c + 2 ^ 59 /\ toZ (snd w) = zlit64 zs + a_off c + ml + 2 ^ 59.
Lemma mk_lw_ok : forall bc D w, In w (mk_lw bc D) -> LWIN_OK bc D w.
Proof.
  intros bc D. induction D as [|[c m] r IH]; intros w H; [destruct H|]. cbn [mk_lw] in H.
  assert (REC : In w (mk_lw bc r) -> LWIN_OK bc ((c, m) :: r) w).
  { intros H0. destruct (IH w H0) as (c' & m' & zs & ml & HI & HR). exists c', m', zs, ml. split; [right; exact HI|exact HR]. }
  destruct (side_lwin bc (c, m)) as [w0|] eqn:ES; [|exact (REC H)].
  destruct H as [<-|H]; [|exact (REC H)].
  unfold side_lwin in ES. cbn [fst snd] in ES. destruct (a_base c) as [zs| | | | | | |] eqn:EB; try discriminate.
  destruct (xloB bc m) as [ml|] eqn:EX; [|discriminate]. cbv zeta in ES.
  destruct (z2b (zlit64 zs + a_off c)) as [l|] eqn:E1; [|discriminate].
  destruct (z2b (zlit64 zs + a_off c + ml)) as [h|] eqn:E2; [|discriminate]. injection ES as <-.
  apply z2b_val in E1. apply z2b_val in E2. exists c, m, zs, ml. split; [left; reflexivity|]. split; [exact EB|]. split; [exact EX|].
  cbn [fst snd]. split; [apply E1|apply E2].
Qed.
Lemma lwin_sound : forall bc D w a e kk z, LWIN_OK bc D w -> toZ (fst w) <= toZ a -> toZ e <= toZ (snd w) ->
  toZ a = kk + 2 ^ 59 -> toZ e = kk + zlit64 z + 2 ^ 59 -> in_sidesB bc D (ELit 0) kk (zlit64 z) = true.
Proof.
  intros bc D w a e kk z (c & m & zs & ml & HI & HB & HX & V1 & V2) L1 L2 Va Ve.
  apply (in_sidesB_intro bc D (ELit 0) kk (zlit64 z) c m HI). unfold sub_itvB.
  match goal with |- (if ?c0 then true else _) = true => destruct c0; [reflexivity|] end.
  rewrite zlit64_range. unfold xinsideB. rewrite HB. cbn [shares_var novars]. unfold xinside_numB.
  cbn [xloB xhiB base_rangeB]. rewrite Z.eqb_refl, HX, zlit64_idem. change (0 mod two64) with 0.
  apply andb_true_intro. split; apply Z.leb_le; lia.
Qed.
Lemma win_in_lw : forall bc D a e kk z, win_in (mk_lw bc D) a e = true -> toZ a = kk + 2 ^ 59 -> toZ e = kk + zlit64 z + 2 ^ 59 ->
  in_sidesB bc D (ELit 0) kk (zlit64 z) = true.
Proof.
  intros bc D a e kk z H Va Ve. destruct (win_in_ex _ _ _ H) as (lo & hi & HI & L1 & L2).
  exact (lwin_sound bc D (lo, hi) a e kk z (mk_lw_ok bc D _ HI) L1 L2 Va Ve).
Qed.

(* [comment removed for export] *)
Definition lit0_iv (K : kentry) : option (PrimInt63.int * PrimInt63.int) :=
  match K with
  | KWord (SA (ELit 0) _) _ _ => ent_iv K
  | KZero (SA (ELit 0) _) (ELit _) | KFill (SA (ELit 0) _) (ELit _) _ | KUnk (SA (ELit 0) _) (ELit _) => ent_iv K
  | _ => None
  end.
Lemma apart_sides : forall bc i1 i2 sp b1 k1 w br2 kb kk l0,
  in_sidesB bc (sp_D sp) kb kk (zlit64 l0) = true -> ranges_apart_pcF bc i1 i2 sp b1 k1 (elen w) br2 kb kk (ELit l0) = true.
Proof.
  intros bc i1 i2 sp b1 k1 w br2 kb kk l0 H. unfold ranges_apart_pcF, elen. cbv zeta.
  match goal with |- (if ?c0 then true else _) = true => destruct c0; [reflexivity|] end.
  match goal with |- (if ?c0 then true else _) = true => destruct c0; [reflexivity|] end. exact H.
Qed.
Lemma lit0_keep : forall bc si xo K a e br2, lit0_iv K = Some (a, e) ->
  win_in (mk_lw bc (sp_D (sx_sp (si_sx si)))) a e = true -> prune1pcKX bc si xo K false br2 None = PKeep.
Proof.
  intros bc si xo K a e br2 HL HW.
  assert (G : forall kb kk m, kdescr K = Some (kb, kk, Some m) -> ent_iv K = Some (a, e) -> toZ a = kk + 2 ^ 59 /\ toZ e = kk + m + 2 ^ 59).
  { intros kb kk m HD HI. exact (ent_iv_descr K a e kb kk m HI HD). }
  destruct K as [[b k] w' v|[b k] len|[b k] len bk|lo hi|e' m'|e' lo' hi'|[b k] n|a1 n1 a2 n2|[b k] len fc|[b k] len];
    cbn [lit0_iv] in HL; try discriminate;
    (destruct b as [zb| | | | | | |]; try discriminate); (destruct zb as [|pb|pb]; try discriminate).
  - (* [comment removed for export] *)
    destruct (G _ _ _ eq_refl HL) as [Va Ve].
    pose proof (win_in_lw bc _ a e k (Z.of_nat w') HW Va Ve) as HS.
    unfold prune1pcKX, prune1pcKF2'. destruct (fastkeep _ _ _ _); [reflexivity|]. unfold prune1pcKF3.
    change (elen w') with (ELit (Z.of_nat w')). rewrite (apart_sides bc _ _ _ _ _ _ _ _ _ _ HS). reflexivity.
  - (* [comment removed for export] *)
    destruct len as [l0| | | | | | |]; try discriminate. destruct (G _ _ _ eq_refl HL) as [Va Ve].
    pose proof (win_in_lw bc _ a e k l0 HW Va Ve) as HS.
    unfold prune1pcKX, prune1pcKF2'. destruct (fastkeep _ _ _ _); [reflexivity|]. unfold prune1pcKF3, zfKF. cbv zeta.
    rewrite (apart_sides bc _ _ _ _ _ _ _ _ _ _ HS). reflexivity.
  - (* [comment removed for export] *)
    destruct len as [l0| | | | | | |]; try discriminate. destruct (G _ _ _ eq_refl HL) as [Va Ve].
    pose proof (win_in_lw bc _ a e k l0 HW Va Ve) as HS.
    unfold prune1pcKX, prune1pcKF2'. destruct (fastkeep _ _ _ _); [reflexivity|]. unfold prune1pcKF3, zfKF. cbv zeta.
    rewrite (apart_sides bc _ _ _ _ _ _ _ _ _ _ HS). reflexivity.
  - (* [comment removed for export] *)
    destruct len as [l0| | | | | | |]; try discriminate. destruct (G _ _ _ eq_refl HL) as [Va Ve].
    pose proof (win_in_lw bc _ a e k l0 HW Va Ve) as HS.
    unfold prune1pcKX, prune1pcKF2'. destruct (fastkeep _ _ _ _); [reflexivity|]. unfold prune1pcKF3, zfKF. cbv zeta.
    rewrite (apart_sides bc _ _ _ _ _ _ _ _ _ _ HS). reflexivity.
Qed.

Fixpoint chainKFW (bc : bctx) (xo : option bx) (fl : list (sxi * list sxi)) (lws : list (list win)) (a e : PrimInt63.int)
         (K : kentry) (okb : option expr) (same_of : positive -> bool) (br2 : option (Z * Z)) : list kentry :=
  match fl, lws with
  | (si, rest) :: fl', W :: lws' =>
      let sx := si_sx si in
      if (if same_of (sx_bid sx) then false else win_in W a e) then chainKFW bc xo fl' lws' a e K okb same_of br2
      else
        match prune1pcKX bc si xo K (same_of (sx_bid sx)) br2 None with
        | PKeep => chainKFW bc xo fl' lws' a e K okb same_of br2
        | PRepl l =>
            match okb with
            | Some kb =>
                flat_map (fun K' => match kbase K' with
                                    | Some kb' => if expr_eqb kb' kb then chainK2F2 bc xo rest K' okb same_of br2 None else chain_slowF bc rest [K']
                                    | None => chain_slowF bc rest [K']
                                    end) l
            | None => chain_slowF bc rest l
            end
        end
  | _, _ => chainKFF2 bc xo fl K okb same_of br2 None
  end.
Lemma chainKFW_eq : forall bc xo K a e okb same_of br2 fl, lit0_iv K = Some (a, e) ->
  chainKFW bc xo fl (map (lw_of bc) fl) a e K okb same_of br2 = chainKFF2 bc xo fl K okb same_of br2 None.
Proof.
  intros bc xo K a e okb same_of br2 fl HL. induction fl as [|[si rest] fl' IH]; [reflexivity|].
  cbn [chainKFW chainKFF2 map]. cbv zeta. unfold lw_of at 1. cbn [fst].
  destruct (same_of (sx_bid (si_sx si))) eqn:ES.
  - rewrite IH. reflexivity.
  - destruct (win_in (mk_lw bc (sp_D (sx_sp (si_sx si)))) a e) eqn:EW.
    + rewrite (lit0_keep bc si xo K a e br2 HL EW). exact IH.
    + rewrite IH. reflexivity.
Qed.

Definition mk_glw (bc : bctx) (gl : ptree (option grp6)) : ptree (list (list win)) :=
  pt_map (fun og : option grp6 =>
            match og with
            | Some g => match k_flo g with [] => [] | _ :: _ => map (lw_of bc) (k_fl g) end
            | None => []
            end) gl.
Fixpoint entriesGF9 (bc : bctx) (X : ptree (option bx)) (sis : list sxi) (gl : ptree (option grp6)) (glw : ptree (list (list win)))
         (kn : list kentry) (infos : list (option einfoF)) : list kentry :=
  match kn, infos with
  | K :: rest, oi :: irest =>
      (match oi with
       | Some ei =>
           match ef_m ei with
           | Some _ =>
               match pt_get gl (ef_gid ei) with
               | Some (Some g) =>
                   match k_flo g with
                   | [] => match k_same g with
                           | SNone => [K]
                           | SClean fl => match ent_iv K with
                                          | Some _ => [K]
                                          | None => chainKFF2 bc (xget X (ef_bid ei)) fl K (kbase K) (sameof K ei) (br2of K ei) None
                                          end
                           | SDirty fl => match ent_iv K with
                                          | Some (a, e) => chainKP bc (xget X (ef_bid ei)) fl a e K (kbase K) (sameof K ei) (br2of K ei)
                                          | None => chainKFF2 bc (xget X (ef_bid ei)) fl K (kbase K) (sameof K ei) (br2of K ei) None
                                          end
                           end
                   | _ :: _ =>
                       match lit0_iv K with
                       | Some (a, e) =>
                           match pt_get glw (ef_gid ei) with
                           | Some lws => chainKFW bc (xget X (ef_bid ei)) (k_fl g) lws a e K (kbase K) (sameof K ei) (br2of K ei)
                           | None => chainKFF2 bc (xget X (ef_bid ei)) (k_fl g) K (kbase K) (sameof K ei) (br2of K ei) None
                           end
                       | None => chainKFF2 bc (xget X (ef_bid ei)) (k_fl g) K (kbase K) (sameof K ei) (br2of K ei) None
                       end
                   end
               | _ => chainK2F2 bc (xget X (ef_bid ei)) sis K (kbase K) (sameof K ei) (br2of K ei) None
               end
           | None =>
               let p := mk_pre bc K (br2of K ei) in
               let enj := enj_of K (br2of K ei) (fst p) (snd p) in
               chainKFF2 bc (xget X (ef_bid ei)) (mk_flX bc (sameof K ei) enj (ksym K) [] sis)
                         K (kbase K) (sameof K ei) (br2of K ei) (Some p)
           end
       | None => if is_fact_entry K then [K] else chainK2F2 bc None sis K None (fun _ => false) None None
       end) ++ entriesGF9 bc X sis gl glw rest irest
  | _, _ => []
  end.
Lemma entriesGF9_eq : forall bc X sis gl kn infos, entriesGF9 bc X sis gl (mk_glw bc gl) kn infos = entriesGF8 bc X sis gl kn infos.
Proof.
  intros bc X sis gl kn. induction kn as [|K rest IH]; intros infos; [reflexivity|]. destruct infos as [|oi irest]; [reflexivity|].
  cbn [entriesGF9 entriesGF8]. rewrite IH. f_equal.
  destruct oi as [ei|]; [|reflexivity]. destruct (ef_m ei); [|reflexivity].
  destruct (pt_get gl (ef_gid ei)) as [[g|]|] eqn:EG; try reflexivity.
  destruct (k_flo g) as [|p0 fl0] eqn:EF; [reflexivity|].
  destruct (lit0_iv K) as [[a e]|] eqn:EL; [|reflexivity].
  unfold mk_glw. rewrite pt_get_map, EG, EF. apply chainKFW_eq. exact EL.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition h2 : PrimInt63.int := Uint63.of_Z 2.
Definition h3 : PrimInt63.int := Uint63.of_Z 3.
Definition h4 : PrimInt63.int := Uint63.of_Z 4.
Definition h5 : PrimInt63.int := Uint63.of_Z 5.
Definition h7 : PrimInt63.int := Uint63.of_Z 7.
Definition h11 : PrimInt63.int := Uint63.of_Z 11.
Definition h13 : PrimInt63.int := Uint63.of_Z 13.
Fixpoint n2h (n : nat) (acc : PrimInt63.int) : PrimInt63.int :=
  match n with
  | S (S (S (S m))) => n2h m (PrimInt63.add acc h4)
  | S (S (S O)) => PrimInt63.add acc h3
  | S (S O) => PrimInt63.add acc h2
  | S O => PrimInt63.add acc i1
  | O => acc
  end.
Fixpoint p2h (p : positive) (acc : PrimInt63.int) : PrimInt63.int :=
  match p with
  | xH => PrimInt63.add (PrimInt63.add acc acc) i1
  | xO q => p2h q (PrimInt63.add acc acc)
  | xI q => p2h q (PrimInt63.add (PrimInt63.add acc acc) i1)
  end.
Definition z2h (z : Z) : PrimInt63.int := match z with Z0 => i0 | Zpos p => p2h p i1 | Zneg p => p2h p h2 end.
Fixpoint hE (e : expr) : PrimInt63.int :=
  match e with
  | ELit z => z2h z
  | EVar n => n2h n h7
  | EAlu _ a b | EAluw _ a b => PrimInt63.add (PrimInt63.mul h3 (hE a)) (PrimInt63.mul h5 (hE b))
  | EMd _ a b | EMdw _ a b => PrimInt63.add (PrimInt63.mul h7 (hE a)) (PrimInt63.mul h11 (hE b))
  | EExt _ _ _ a => PrimInt63.add (hE a) h13
  | EBlob _ _ _ _ => h13
  end.
Definition hs_of (D : list (saddr * expr)) : list PrimInt63.int := map (fun cm => hE (a_base (fst cm))) D.
Fixpoint in_sides_numH (bc : bctx) (D : list (saddr * expr)) (hs : list PrimInt63.int) (b : expr) (hb : PrimInt63.int) (k n : Z) : bool :=
  match D, hs with
  | (c, m) :: r, h :: hr =>
      if PrimInt63.eqb h hb then (if num_subF bc b k n c m then true else in_sides_numH bc r hr b hb k n)
      else in_sides_numH bc r hr b hb k n
  | _, _ => in_sides_numF bc D b k n
  end.
Lemma in_sides_numH_eq : forall bc D b k n, in_sides_numH bc D (hs_of D) b (hE b) k n = in_sides_num bc D b k n.
Proof.
  intros bc D b k n. induction D as [|[c m] r IH]; [reflexivity|]. cbn [hs_of map in_sides_numH in_sides_num fst]. fold (hs_of r). rewrite IH.
  destruct (PrimInt63.eqb (hE (a_base c)) (hE b)) eqn:EH.
  - unfold num_subF, num_sub. rewrite BLKF.expr_eqbF_eq. reflexivity.
  - assert (EN : num_sub bc b k n c m = false).
    { unfold num_sub. destruct (expr_eqb b (a_base c)) eqn:E; [|reflexivity].
      apply p_expr_eqb_eq in E. rewrite E, Uint63Axioms.eqb_refl in EH. discriminate. }
    rewrite EN. reflexivity.
Qed.
(* [comment removed for export] *)
Definition rcache : Type := option (option (PrimInt63.int * PrimInt63.int)).
Definition abs_of (bc : bctx) (b : expr) (glo ghi : Z) : option (PrimInt63.int * PrimInt63.int) :=
  match base_rangeB bc b with
  | Some (lo1, hi1) => match z2b (lo1 + glo) with
                       | Some a => match z2b (hi1 + ghi) with Some e => Some (a, e) | None => None end
                       | None => None
                       end
  | None => None
  end.
Definition get_abs (bc : bctx) (rc : rcache) (b : expr) (glo ghi : Z) : option (PrimInt63.int * PrimInt63.int) * rcache :=
  match rc with Some r => (r, rc) | None => let r := abs_of bc b glo ghi in (r, Some r) end.
Definition RC_OK (bc : bctx) (glo ghi : Z) (gx : option gxi) (rc : rcache) : Prop :=
  match gx with Some x => forall r, rc = Some r -> r = abs_of bc (gx_b x) glo ghi | None => True end.
Lemma abs_sound : forall bc D b glo ghi a e, abs_of bc b glo ghi = Some (a, e) -> win_in (mk_lw bc D) a e = true ->
  0 <= ghi - glo < two63z -> in_sidesB bc D b glo (ghi - glo) = true.
Proof.
  intros bc D b glo ghi a e HA HW HG. unfold abs_of in HA.
  destruct (base_rangeB bc b) as [[lo1 hi1]|] eqn:EB; [|discriminate].
  destruct (z2b (lo1 + glo)) as [a'|] eqn:E1; [|discriminate]. destruct (z2b (hi1 + ghi)) as [e'|] eqn:E2; [|discriminate].
  injection HA as <- <-. apply z2b_val in E1. apply z2b_val in E2. destruct E1 as [Va _]. destruct E2 as [Ve _].
  destruct (win_in_ex _ _ _ HW) as (lo & hi & HI & L1 & L2).
  destruct (mk_lw_ok bc D (lo, hi) HI) as (c & m & zs & ml & HD & HB & HX & V1 & V2). cbn [fst snd] in V1, V2.
  apply (in_sidesB_intro bc D b glo (ghi - glo) c m HD). unfold sub_itvB.
  match goal with |- (if ?c0 then true else _) = true => destruct c0; [reflexivity|] end.
  assert (G2 : (Z.leb 0 (ghi - glo) && Z.ltb (ghi - glo) two64)%bool = true).
  { apply andb_true_intro. split; [apply Z.leb_le; lia|apply Z.ltb_lt]. unfold two63z in HG. unfold two64. lia. }
  rewrite G2. unfold xinsideB. rewrite HB. cbn [shares_var novars]. unfold xinside_numB.
  cbn [xloB xhiB]. rewrite Z.eqb_refl, EB, HX.
  assert (EZ : zlit64 (ghi - glo) = ghi - glo) by (unfold zlit64; rewrite G2; reflexivity). rewrite EZ.
  apply andb_true_intro. split; apply Z.leb_le; lia.
Qed.
Definition linV2MA (bc : bctx) (si : sxi) (hs : list PrimInt63.int) (lw : list win) (ghb : PrimInt63.int) (b : positive) (glo ghi : Z)
           (gx : option gxi) (m : smemo) (rc : rcache) : bool * smemo * rcache :=
  match gx with
  | Some x =>
      if Pos.eqb b (sx_bid (si_sx si)) then (false, m, rc) else
      if (if Z.leb 0 (ghi - glo) then Z.ltb (ghi - glo) two63z else false) then
        let sx := si_sx si in
        if in_sides_numH bc (sp_D (sx_sp sx)) hs (gx_b x) ghb glo (ghi - glo) then (true, m, rc)
        else if lin_apartF bc (si_bx si) (gx_bx x) (a_base (sx_a sx)) (a_off (sx_a sx)) (zlit64F (Z.of_nat (sx_w sx))) (gx_b x) glo (ghi - glo) then (true, m, rc)
        else
          let '(ab, rc') := get_abs bc rc (gx_b x) glo ghi in
          if (match ab with Some (a, e) => win_in lw a e | None => false end) then (true, m, rc')
          else let '(v, m') := in_sidesM bc m (sp_D (sx_sp sx)) (gx_b x) glo (ghi - glo) in (v, m', rc')
      else (false, m, rc)
  | None => (false, m, rc)
  end.
Definition ghb_of (gx : option gxi) : PrimInt63.int := match gx with Some x => hE (gx_b x) | None => i0 end.
Lemma linV2MA_ok : forall bc si b glo ghi gx m rc, GMEMO bc glo ghi gx m -> RC_OK bc glo ghi gx rc ->
  fst (fst (linV2MA bc si (hs_of (sp_D (sx_sp (si_sx si)))) (mk_lw bc (sp_D (sx_sp (si_sx si)))) (ghb_of gx) b glo ghi gx m rc)) = linV2 bc si b glo ghi gx /\
  GMEMO bc glo ghi gx (snd (fst (linV2MA bc si (hs_of (sp_D (sx_sp (si_sx si)))) (mk_lw bc (sp_D (sx_sp (si_sx si)))) (ghb_of gx) b glo ghi gx m rc))) /\
  RC_OK bc glo ghi gx (snd (linV2MA bc si (hs_of (sp_D (sx_sp (si_sx si)))) (mk_lw bc (sp_D (sx_sp (si_sx si)))) (ghb_of gx) b glo ghi gx m rc)).
Proof.
  intros bc si b glo ghi gx m rc HM HR. unfold linV2MA, linV2, ghb_of. destruct gx as [x|]; [|OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption]. cbn [GMEMO RC_OK] in *.
  destruct (Pos.eqb b (sx_bid (si_sx si))); [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption|].
  destruct (if Z.leb 0 (ghi - glo) then Z.ltb (ghi - glo) two63z else false) eqn:EG; [|OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption]. cbv zeta.
  rewrite in_sides_numH_eq.
  destruct (in_sides_num bc (sp_D (sx_sp (si_sx si))) (gx_b x) glo (ghi - glo)); [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption|].
  destruct (lin_apartF _ _ _ _ _ _ _ _ _); [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption|].
  assert (HG : 0 <= ghi - glo < two63z).
  { destruct (Z.leb_spec 0 (ghi - glo)); [|discriminate]. apply Z.ltb_lt in EG. lia. }
  assert (HR' : forall r, snd (get_abs bc rc (gx_b x) glo ghi) = Some r -> r = abs_of bc (gx_b x) glo ghi).
  { unfold get_abs. destruct rc as [r0|]; cbn [snd]; [exact HR|]. intros r E. injection E as <-. reflexivity. }
  assert (HA : fst (get_abs bc rc (gx_b x) glo ghi) = abs_of bc (gx_b x) glo ghi).
  { unfold get_abs. destruct rc as [r0|]; cbn [fst]; [exact (HR r0 eq_refl)|reflexivity]. }
  destruct (get_abs bc rc (gx_b x) glo ghi) as [ab rc']. cbn [fst snd] in HR', HA.
  destruct (match ab with Some (a, e) => win_in (mk_lw bc (sp_D (sx_sp (si_sx si)))) a e | None => false end) eqn:EW.
  - cbn [fst snd]. split; [|split; assumption].
    destruct ab as [[a e]|]; [|discriminate]. symmetry. exact (abs_sound bc _ (gx_b x) glo ghi a e (eq_sym HA) EW HG).
  - destruct (in_sidesM_ok bc (sp_D (sx_sp (si_sx si))) (gx_b x) glo (ghi - glo) m HM) as [E1 E2].
    destruct (in_sidesM bc m (sp_D (sx_sp (si_sx si))) (gx_b x) glo (ghi - glo)) as [v m']. cbn [fst snd] in *.
    split; [exact E1|]. split; assumption.
Qed.
Fixpoint mk_flMA (bc : bctx) (b : positive) (glo ghi : Z) (gx : option gxi) (gqj : option (PrimInt63.int * PrimInt63.int)) (ghb : PrimInt63.int)
         (same_skip : bool) (m : smemo) (rc : rcache) (sis : list sxi) (hss : list (list PrimInt63.int)) (lws : list (list win)) : list (sxi * list sxi) :=
  match sis, hss, lws with
  | si :: srest, hs :: hrest, lw :: lrest =>
      if Pos.eqb b (sx_bid (si_sx si)) then
        (if same_skip then mk_flMA bc b glo ghi gx gqj ghb same_skip m rc srest hrest lrest
         else (si, srest) :: mk_flMA bc b glo ghi gx gqj ghb same_skip m rc srest hrest lrest)
      else if verdictJ si b gqj then mk_flMA bc b glo ghi gx gqj ghb same_skip m rc srest hrest lrest
      else let '(vm, rc') := linV2MA bc si hs lw ghb b glo ghi gx m rc in
           if fst vm then mk_flMA bc b glo ghi gx gqj ghb same_skip (snd vm) rc' srest hrest lrest
           else (si, srest) :: mk_flMA bc b glo ghi gx gqj ghb same_skip (snd vm) rc' srest hrest lrest
  | _, _, _ => mk_flM bc b glo ghi gx gqj same_skip m sis
  end.
Definition hss_of (sis : list sxi) : list (list PrimInt63.int) := map (fun si => hs_of (sp_D (sx_sp (si_sx si)))) sis.
Definition lws_of (bc : bctx) (sis : list sxi) : list (list win) := map (fun si => mk_lw bc (sp_D (sx_sp (si_sx si)))) sis.
Lemma mk_flMA_eq : forall bc b glo ghi gx gqj sis m rc, GMEMO bc glo ghi gx m -> RC_OK bc glo ghi gx rc ->
  mk_flMA bc b glo ghi gx gqj (ghb_of gx) true m rc sis (hss_of sis) (lws_of bc sis) = mk_flG (skipo5 bc b glo ghi gx gqj) sis /\
  mk_flMA bc b glo ghi gx gqj (ghb_of gx) false m rc sis (hss_of sis) (lws_of bc sis) = mk_flG (skipv5 bc b glo ghi gx gqj) sis.
Proof.
  intros bc b glo ghi gx gqj sis. unfold hss_of, lws_of. induction sis as [|si rest IH]; intros m rc HM HR.
  - split; [exact (proj1 (mk_flM_eq bc b glo ghi gx gqj [] m HM))|exact (proj2 (mk_flM_eq bc b glo ghi gx gqj [] m HM))].
  - cbn [mk_flMA mk_flG map]. unfold skipo5 at 1, skipv5 at 1 2.
    destruct (Pos.eqb b (sx_bid (si_sx si))) eqn:EB.
    + destruct (IH m rc HM HR) as [I1 I2]. split; [exact I1|].
      assert (EV : verdictJ si b gqj = false) by (unfold verdictJ; rewrite EB; reflexivity).
      assert (EL : linV2 bc si b glo ghi gx = false) by (unfold linV2; destruct gx; [rewrite EB|]; reflexivity).
      rewrite EV, EL, I2. reflexivity.
    + destruct (verdictJ si b gqj); [exact (IH m rc HM HR)|].
      destruct (linV2MA_ok bc si b glo ghi gx m rc HM HR) as (E1 & E2 & E3).
      destruct (linV2MA bc si (hs_of (sp_D (sx_sp (si_sx si)))) (mk_lw bc (sp_D (sx_sp (si_sx si)))) (ghb_of gx) b glo ghi gx m rc) as [[v m'] rc'].
      cbn [fst snd] in E1, E2, E3 |- *. rewrite <- E1.
      destruct (IH m' rc' E2 E3) as [I1 I2]. destruct v; [split; assumption|]. rewrite I1, I2. split; reflexivity.
Qed.
Definition mk_glF7 (bc : bctx) (info : ptree binfo) (X : ptree (option bx)) (bnds : gtab) (sis : list sxi) (sbl : list sbe) : ptree (option grp6) :=
  let hss := hss_of sis in
  let lws := lws_of bc sis in
  pt_map (fun g : gval =>
     match g with
     | (b, _, (glo, ghi)) =>
         match pt_get info b with
         | Some bi =>
             let gx := if is_litb (bi_base bi) then None else Some (GXI (bi_base bi) (xget X b)) in
             let gqj := gqj_of (match bi_br bi with Some (lo2, hi2) => Some (glo + lo2, ghi + hi2) | None => None end) in
             let flo := if forallbF (fun e => if Pos.eqb b (sbe_b e) then true else hv_other (sbe_h e) gqj) sbl then []
                        else mk_flMA bc b glo ghi gx gqj (ghb_of gx) true [] None sis hss lws in
             Some (GRP6 flo
                        (match flo with [] => [] | _ :: _ => mk_flMA bc b glo ghi gx gqj (ghb_of gx) false [] None sis hss lws end)
                        (match sb_find sbl b with
                         | Some e => if hv_same (sbe_h e) (match z2b glo with Some a => match z2b ghi with Some e' => Some (a, e') | None => None end | None => None end)
                                     then SClean (sbe_fl e) else SDirty (sbe_fl e)
                         | None => SNone
                         end))
         | None => None
         end
     end) bnds.
Lemma pt_map_ext : forall (A B : Type) (f g : A -> B) t, (forall x, f x = g x) -> pt_map f t = pt_map g t.
Proof.
  intros A B f g t H. induction t as [|l IHl o r IHr]; [reflexivity|]. cbn [pt_map]. rewrite IHl, IHr. destruct o; [rewrite H|]; reflexivity.
Qed.
Lemma mk_glF7_eq : forall bc info X bnds sis sbl, mk_glF7 bc info X bnds sis sbl = mk_glF6 bc info X bnds sis sbl.
Proof.
  intros. unfold mk_glF7, mk_glF6. cbv zeta. apply pt_map_ext. intros [[b o] [glo ghi]].
  destruct (pt_get info b) as [bi|]; [|reflexivity].
  set (gx := if is_litb (bi_base bi) then None else Some (GXI (bi_base bi) (xget X b))).
  set (gqj := gqj_of (match bi_br bi with Some (lo2, hi2) => Some (glo + lo2, ghi + hi2) | None => None end)).
  assert (GM0 : GMEMO bc glo ghi gx []) by (destruct gx as [x|]; [intros c e r []|exact I]).
  assert (RC0 : RC_OK bc glo ghi gx None) by (destruct gx as [x|]; [intros r E; discriminate E|exact I]).
  destruct (mk_flMA_eq bc b glo ghi gx gqj sis [] None GM0 RC0) as [A1 A2].
  destruct (mk_flM_eq bc b glo ghi gx gqj sis [] GM0) as [B1 B2].
  rewrite A1, A2, B1, B2. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition carryGF10C (bc : bctx) (log : list sentry) (scs : list sprep) (kn : list kentry) : list kentry :=
  let '(sxs, t0) := mk_stxsC3 log scs nt_empty in
  let '(r, gs) := scanF2 bc kn t0 gst_empty None None in
  let '(infos, t1) := r in
  let sbs := store_bases sxs PTLeaf in
  let X := pt_map (fun bi => if existsbF (fun sb => shares_var sb (bi_base bi)) sbs then Some (mk_bx bc (bi_base bi)) else None) (nt_info t1) in
  let sis := map (mk_sxi X) sxs in
  let sbl := mk_sbl sis sis [] in
  let gl := mk_glF7 bc (nt_info t1) X (gs_bnds gs) sis sbl in
  stores_partX2 bc sis sbl ++ entriesGF9 bc X sis gl (mk_glw bc gl) kn infos.
Lemma carryGF10C_eq : forall bc log scs kn, carryGF10C bc log scs kn = carryGF9C bc log scs kn.
Proof.
  intros bc log scs kn. unfold carryGF10C, carryGF9C.
  destruct (mk_stxsC3 log scs nt_empty) as [sxs t0]. destruct (scanF2 bc kn t0 gst_empty None None) as [[infos t1] gs]. cbv zeta.
  rewrite entriesGF9_eq, mk_glF7_eq.
  rewrite stores_partX2_eq. reflexivity.
Qed.
(* [comment removed for export] *)
Definition carryGF11C (bc : bctx) (log : list sentry) (scs : list sprep) (kn : list kentry) : list kentry :=
  let '(sxs, t0) := mk_stxsC3 log scs nt_empty in
  let '(r, gs) := scanF2 bc kn t0 gst_empty None None in
  let '(infos, t1) := r in
  let sbs := store_bases sxs PTLeaf in
  let X := pt_map (fun bi => if existsbF (fun sb => shares_var sb (bi_base bi)) sbs then Some (mk_bx bc (bi_base bi)) else None) (nt_info t1) in
  let sis := map (mk_sxi X) sxs in
  let sbl := mk_sbl sis sis [] in
  let gl := mk_glF7 bc (nt_info t1) X (gs_bnds gs) sis sbl in
  stores_partX3 bc sis sbl ++ entriesGF9 bc X sis gl (mk_glw bc gl) kn infos.
Lemma carryGF11C_eq : forall bc log kn,
  carryGF11C bc log (map (mk_sctx bc (mk_bext bc)) log) kn = carryGF10C bc log (map (mk_sctx bc (mk_bext bc)) log) kn.
Proof.
  intros bc log kn. unfold carryGF11C, carryGF10C. rewrite mk_stxsC3_eq, mk_stxsC2_eq.
  destruct (mk_stxs bc log nt_empty) as [sxs t0] eqn:E0.
  destruct (mk_stxs_okG _ _ _ _ _ (NTI_empty bc) E0) as (HT0 & HS0 & _).
  destruct (scanF2 bc kn t0 gst_empty None None) as [[infos t1] gs]. cbv zeta. f_equal.
  rewrite (stores_partX3_eq bc _ t0 sxs (XOK_map _ _ _) HS0), stores_partX2_eq.
  match goal with |- context [mk_sbl ?s ?s []] => destruct (mk_sbl_ok s s [] (fun e (H : In e []) => match H with end)) as (HSB1 & HSB2 & _);
    rewrite (stores_partX_eq bc s s (mk_sbl s s []) HSB1 HSB2) end.
  symmetry. match goal with |- context [mk_sbl ?s ?s []] => destruct (mk_sbl_ok s s [] (fun e (H : In e []) => match H with end)) as (HSB3 & HSB4 & _) end.
  exact (stores_partF5_eq bc _ t0 _ sxs _ (XOK_map _ _ _) HS0 HSB3 HSB4 (fun si H => H)).
Qed.
Definition carryKF_ctx3 (bc : bctx) (log : list sentry) (scs : list sprep) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match log, hints with
  | [], _ => (kn, [], hints)
  | _, [] => (carryGF11C bc log scs kn, [], [])
  | _, _ => carryB bc log kn hints
  end.
Definition carryKF_ctx2 (bc : bctx) (log : list sentry) (scs : list sprep) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match log, hints with
  | [], _ => (kn, [], hints)
  | _, [] => (carryGF10C bc log scs kn, [], [])
  | _, _ => carryB bc log kn hints
  end.
Lemma carryKF_ctx2_eq : forall bc log scs kn hints, carryKF_ctx2 bc log scs kn hints = carryKF_ctx bc log scs kn hints.
Proof. intros. unfold carryKF_ctx2, carryKF_ctx. destruct log; [reflexivity|]. destruct hints; [|reflexivity]. rewrite carryGF10C_eq. reflexivity. Qed.
Lemma carryKF_ctx3_eq : forall bc log kn hints,
  carryKF_ctx3 bc log (map (mk_sctx bc (mk_bext bc)) log) kn hints = carryKF_ctx bc log (map (mk_sctx bc (mk_bext bc)) log) kn hints.
Proof.
  intros. rewrite <- carryKF_ctx2_eq. unfold carryKF_ctx3, carryKF_ctx2. destruct log as [|s0 older]; [reflexivity|]. destruct hints; [|reflexivity].
  rewrite carryGF11C_eq. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sdmemo : Type := list (saddr * expr * sidet).
Fixpoint sd_find (sm : sdmemo) (c : saddr) (m : expr) : option sidet :=
  match sm with
  | [] => None
  | (c', m', s) :: r =>
      if (if expr_eqbF (a_base c) (a_base c') then if Z.eqb (a_off c) (a_off c') then expr_eqbF m m' else false else false) then Some s
      else sd_find r c m
  end.
Definition SDM_OK (bc : bctx) (b1 : expr) (bi : binf) (sm : sdmemo) : Prop := forall c m s, In (c, m, s) sm -> s = mk_sidet bc b1 bi c m.
Lemma sd_find_ok : forall bc b1 bi sm c m s, SDM_OK bc b1 bi sm -> sd_find sm c m = Some s -> s = mk_sidet bc b1 bi c m.
Proof.
  intros bc b1 bi sm c m s. induction sm as [|[[c' m'] s'] r IH]; intros H HF; [discriminate|]. cbn [sd_find] in HF.
  destruct (if expr_eqbF (a_base c) (a_base c') then if Z.eqb (a_off c) (a_off c') then expr_eqbF m m' else false else false) eqn:E.
  - injection HF as <-. destruct (expr_eqbF (a_base c) (a_base c')) eqn:E1; [|discriminate].
    destruct (Z.eqb_spec (a_off c) (a_off c')) as [E2|]; [|discriminate].
    rewrite BLKF.expr_eqbF_eq in E1, E. apply p_expr_eqb_eq in E1. apply p_expr_eqb_eq in E. subst m'.
    destruct c as [cb co], c' as [cb' co']. cbn [a_base a_off] in *. subst cb' co'. apply H. left. reflexivity.
  - apply IH; [intros c0 m0 s0 H0; apply H; right; exact H0|exact HF].
Qed.
Definition mk_sidetM2 (bc : bctx) (B : bmemo) (sm : sdmemo) (b1 : expr) (bi : binf) (c : saddr) (m : expr) : sidet * bmemo * sdmemo :=
  if shares_var b1 (a_base c) then
    match sd_find sm c m with
    | Some s => (s, B, sm)
    | None => let '(s, B') := mk_sidetM bc B b1 bi c m in (s, B', (c, m, s) :: sm)
    end
  else let '(s, B') := mk_sidetM bc B b1 bi c m in (s, B', sm).
Lemma mk_sidetM2_ok : forall bc b1 bi c m B sm, BOK bc B -> SDM_OK bc b1 bi sm ->
  fst (fst (mk_sidetM2 bc B sm b1 bi c m)) = mk_sidet bc b1 bi c m /\ BOK bc (snd (fst (mk_sidetM2 bc B sm b1 bi c m))) /\
  SDM_OK bc b1 bi (snd (mk_sidetM2 bc B sm b1 bi c m)).
Proof.
  intros bc b1 bi c m B sm HB HS. unfold mk_sidetM2.
  destruct (mk_sidetM_ok bc b1 bi c m B HB) as [E1 H1].
  destruct (shares_var b1 (a_base c)).
  - destruct (sd_find sm c m) as [s|] eqn:EF.
    + cbn [fst snd]. split; [exact (sd_find_ok bc b1 bi sm c m s HS EF)|]. split; assumption.
    + destruct (mk_sidetM bc B b1 bi c m) as [s B']. cbn [fst snd] in *. split; [exact E1|]. split; [exact H1|].
      intros c0 m0 s0 [E|H0]; [injection E as <- <- <-; exact E1|exact (HS c0 m0 s0 H0)].
  - destruct (mk_sidetM bc B b1 bi c m) as [s B']. cbn [fst snd] in *. split; [exact E1|]. split; assumption.
Qed.
Fixpoint mk_rowsM2 (bc : bctx) (B : bmemo) (sm : sdmemo) (b1 : expr) (bi : binf) (kd : list kentry) : list wrow * bmemo * sdmemo :=
  match kd with
  | [] => ([], B, sm)
  | KDisj c1 m1 c2 m2 :: rest =>
      let '(s1, B1, sm1) := mk_sidetM2 bc B sm b1 bi c1 m1 in
      let '(s2, B2, sm2) := mk_sidetM2 bc B1 sm1 b1 bi c2 m2 in
      let '(rows, B3, sm3) := mk_rowsM2 bc B2 sm2 b1 bi rest in
      ((if (if sd_dead s1 then sd_dead s2 else false) then rows else WR c1 m1 s1 c2 m2 s2 :: rows), B3, sm3)
  | _ :: rest => mk_rowsM2 bc B sm b1 bi rest
  end.
Lemma mk_rowsM2_ok : forall bc b1 bi kd B sm, BOK bc B -> SDM_OK bc b1 bi sm ->
  fst (fst (mk_rowsM2 bc B sm b1 bi kd)) = mk_rows bc b1 bi kd /\ BOK bc (snd (fst (mk_rowsM2 bc B sm b1 bi kd))).
Proof.
  intros bc b1 bi kd. induction kd as [|K rest IH]; intros B sm HB HS; [split; [reflexivity|exact HB]|].
  destruct K as [a w' v|a len|a len bk|lo hi|e' m'|e' lo' hi'|a en|c1 m1 c2 m2|a len fc|a len]; cbn [mk_rowsM2 mk_rows]; try exact (IH B sm HB HS).
  destruct (mk_sidetM2_ok bc b1 bi c1 m1 B sm HB HS) as (E1 & H1 & S1). destruct (mk_sidetM2 bc B sm b1 bi c1 m1) as [[s1 B1] sm1]. cbn [fst snd] in E1, H1, S1.
  destruct (mk_sidetM2_ok bc b1 bi c2 m2 B1 sm1 H1 S1) as (E2 & H2 & S2). destruct (mk_sidetM2 bc B1 sm1 b1 bi c2 m2) as [[s2 B2] sm2]. cbn [fst snd] in E2, H2, S2.
  destruct (IH B2 sm2 H2 S2) as [E3 H3]. destruct (mk_rowsM2 bc B2 sm2 b1 bi rest) as [[rows B3] sm3]. cbn [fst snd] in *.
  rewrite <- E1, <- E2, <- E3. split; [|exact H3]. destruct (if sd_dead s1 then sd_dead s2 else false); reflexivity.
Qed.
Definition mk_wtabM2 (bc : bctx) (B : bmemo) (kd : list kentry) (b1 : expr) : wtab * bmemo :=
  let bi := mk_binf bc b1 in
  let '(rb, _) := mk_rowsM2 bc B [] b1 bi kd in (WT (bi_rng bi) (fst rb), snd rb).
Lemma mk_wtabM2_ok : forall bc kd b1 B, BOK bc B -> fst (mk_wtabM2 bc B kd b1) = mk_wtab bc kd b1 /\ BOK bc (snd (mk_wtabM2 bc B kd b1)).
Proof.
  intros bc kd b1 B H. unfold mk_wtabM2, mk_wtab.
  destruct (mk_rowsM2_ok bc b1 (mk_binf bc b1) kd B [] H (fun c m s (HI : In (c, m, s) []) => match HI with end)) as [E1 H1].
  destruct (mk_rowsM2 bc B [] b1 (mk_binf bc b1) kd) as [[rows B1] sm1]. cbn [fst snd] in *. rewrite <- E1. split; [reflexivity|exact H1].
Qed.
Definition mk_sctx_c2 (bc : bctx) (ex : bext) (c : wcache) (s : sentry) : sprep * wcache :=
  match s with
  | SE a w v =>
      match wc_find (snd c) (a_base a) with
      | Some t => (mk_sctxW bc (be_kd ex) t a w, c)
      | None => let '(t, B') := mk_wtabM2 bc (fst c) (be_kd ex) (a_base a) in (mk_sctxW bc (be_kd ex) t a w, (B', (a_base a, t) :: snd c))
      end
  end.
Lemma mk_sctx_c2_fst : forall bc ex c s, WCOK bc ex c -> fst (mk_sctx_c2 bc ex c s) = mk_sctx bc ex s.
Proof.
  intros bc ex [B c] [a w v] [HB HC]. unfold mk_sctx_c2, mk_sctx. cbn [fst snd].
  destruct (wc_find c (a_base a)) as [t|] eqn:EF; cbn [fst].
  - rewrite (wc_find_ok bc ex c _ t HC EF). apply mk_sctxW_eq.
  - destruct (mk_wtabM2_ok bc (be_kd ex) (a_base a) B HB) as [E1 _]. destruct (mk_wtabM2 bc B (be_kd ex) (a_base a)) as [t B']. cbn [fst] in *.
    rewrite E1. apply mk_sctxW_eq.
Qed.
Lemma mk_sctx_c2_ok : forall bc ex c s, WCOK bc ex c -> WCOK bc ex (snd (mk_sctx_c2 bc ex c s)).
Proof.
  intros bc ex [B c] [a w v] [HB HC]. unfold mk_sctx_c2. cbn [fst snd].
  destruct (wc_find c (a_base a)) as [t|] eqn:EF; cbn [snd]; [split; assumption|].
  destruct (mk_wtabM2_ok bc (be_kd ex) (a_base a) B HB) as [E1 H1]. destruct (mk_wtabM2 bc B (be_kd ex) (a_base a)) as [t B']. cbn [fst snd] in *.
  split; [exact H1|]. intros b t0 [E|Hin]; [injection E as <- <-; exact E1|exact (HC b t0 Hin)].
Qed.

Definition lupd2 (bc : bctx) (ex : bext) (i : instr) (ss' : sym_state) (lis : list sprep) (lia : list EXF.sann) (gl : list EXF.lgroup)
           (wc : wcache) : list sprep * list EXF.sann * list EXF.lgroup * wcache :=
  if EXF.is_store_instr i then
    match s_log ss' with
    | e :: _ => let '(sp, wc') := mk_sctx_c2 bc ex wc e in
                let sa := EXF.sann_sp sp e in
                (sp :: lis, sa :: lia, EXF.gl_adde gl e sa, wc')
    | [] => (lis, lia, gl, wc)
    end
  else (lis, lia, gl, wc).
Lemma lupd2_rel : forall bc ex i ss' lis lia gl wc wc2, WCOK bc ex wc -> WCOK bc ex wc2 ->
  fst (lupd2 bc ex i ss' lis lia gl wc2) = fst (EXF.lupd bc ex i ss' lis lia gl wc) /\
  WCOK bc ex (snd (lupd2 bc ex i ss' lis lia gl wc2)) /\ WCOK bc ex (snd (EXF.lupd bc ex i ss' lis lia gl wc)).
Proof.
  intros bc ex i ss' lis lia gl wc wc2 H1 H2. unfold lupd2, EXF.lupd.
  destruct (EXF.is_store_instr i); [|cbn [fst snd]; split; [reflexivity|split; assumption]].
  destruct (s_log ss') as [|e rest]; [cbn [fst snd]; split; [reflexivity|split; assumption]|].
  pose proof (mk_sctx_c2_fst bc ex wc2 e H2) as F2. pose proof (mk_sctx_c2_ok bc ex wc2 e H2) as O2.
  pose proof (mk_sctx_c_fst bc ex wc e H1) as F1. pose proof (mk_sctx_c_ok bc ex wc e H1) as O1.
  destruct (mk_sctx_c2 bc ex wc2 e) as [sp2 wc2']. destruct (mk_sctx_c bc ex wc e) as [sp1 wc1']. cbn [fst snd] in *.
  subst sp2 sp1. split; [reflexivity|split; assumption].
Qed.

Import APC.
Section WithSegs.
Variable segs : list Segment.
Variable IT : itab.
Variable nx0 : nat.
Fixpoint goL2 (bc : bctx) (kn : list kentry) (okx : option (kix * EXF.xctx)) (ex : bext) (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state)
  (lis : list sprep) (lia : list EXF.sann) (gl : list EXF.lgroup) (ck : sym_state) (cklis : list sprep)
  (cklia : list EXF.sann) (ckgl : list EXF.lgroup) (wc : wcache) (c : BASF.bcache) (xm : EXF.xmemo) (rm : BASF.rmemo) (stt : ptree unit) : sym_state * list sprep :=
  match fuel with
  | O => if s_clean ss then (ss, lis) else (ck, cklis)
  | S f =>
      if (if first then false else EXF.is_stopF stt stops (s_pc ss)) then (if s_clean ss then (ss, lis) else (ck, cklis)) else
      match itab_lookup t (s_pc ss) with
      | None => if s_clean ss then (ss, lis) else (ck, cklis)
      | Some i =>
          let '(kx, xc, okx') :=
            if EXF.needs_kx i then
              match okx with
              | Some (kx, xc) => (kx, xc, okx)
              | None => let kx := BLKF.mk_kix_f kn in let xc := EXF.mk_xc segs kx in (kx, xc, Some (kx, xc))
              end
            else (EXF.kx_nil, EXF.xc_nil, okx) in
          let '(r, c', xm', rm') := EXF.sym_stepXBIFx segs bc kx xc ex lis lia gl c xm rm K i ss scr_nil in
          match r with
          | SOk ss' [] _ =>
              if EXF.is_store_instr i then
                let '(lis', lia', gl', wc') := lupd2 bc ex i ss' lis lia gl wc in
                if s_clean ss' then goL2 bc kn okx' ex t K f false stops ss' lis' lia' gl' ss' lis' lia' gl' wc' c' xm' rm' stt
                else goL2 bc kn okx' ex t K f false stops ss' lis' lia' gl' ck cklis cklia ckgl wc' c' xm' rm' stt
              else
                if s_clean ss' then goL2 bc kn okx' ex t K f false stops ss' lis lia gl ss' lis lia gl wc c' xm' rm' stt
                else goL2 bc kn okx' ex t K f false stops ss' lis lia gl ck cklis cklia ckgl wc c' xm' rm' stt
          | _ => if s_clean ss then (ss, lis) else (ck, cklis)
          end
      end
  end.
Lemma goL2_eq : forall bc kn ex t K fuel okx first stops ss lis lia gl ck cklis cklia ckgl wc wc2 c xm rm stt,
  WCOK bc ex wc -> WCOK bc ex wc2 ->
  goL2 bc kn okx ex t K fuel first stops ss lis lia gl ck cklis cklia ckgl wc2 c xm rm stt
  = EXF.sym_execTXBIF_goL segs bc kn okx ex t K fuel first stops ss lis lia gl ck cklis cklia ckgl wc c xm rm stt.
Proof.
  intros bc kn ex t K fuel. induction fuel as [|f IH]; intros okx first stops ss lis lia gl ck cklis cklia ckgl wc wc2 c xm rm stt H1 H2; [reflexivity|].
  cbn [goL2 EXF.sym_execTXBIF_goL].
  destruct (if first then false else EXF.is_stopF stt stops (s_pc ss)); [reflexivity|].
  destruct (itab_lookup t (s_pc ss)) as [i|]; [|reflexivity].
  destruct (if EXF.needs_kx i then match okx with Some (kx, xc) => (kx, xc, okx) | None => (BLKF.mk_kix_f kn, EXF.mk_xc segs (BLKF.mk_kix_f kn), Some (BLKF.mk_kix_f kn, EXF.mk_xc segs (BLKF.mk_kix_f kn))) end
            else (EXF.kx_nil, EXF.xc_nil, okx)) as [[kx xc] okx1].
  destruct (EXF.sym_stepXBIFx segs bc kx xc ex lis lia gl c xm rm K i ss scr_nil) as [[[r c'] xm'] rm'].
  destruct r as [ss' [|sc scs] scr'|]; try reflexivity.
  destruct (EXF.is_store_instr i).
  - destruct (lupd2_rel bc ex i ss' lis lia gl wc wc2 H1 H2) as (E & O2 & O1).
    destruct (lupd2 bc ex i ss' lis lia gl wc2) as [[[lis2 lia2] gl2] wc2']. destruct (EXF.lupd bc ex i ss' lis lia gl wc) as [[[lis1 lia1] gl1] wc1'].
    cbn [fst snd] in E, O1, O2. injection E as -> -> ->. destruct (s_clean ss'); apply IH; assumption.
  - destruct (s_clean ss'); apply IH; assumption.
Qed.
Definition sym_execTXBIFL2 (bc : bctx) (kn : list kentry) (ex : bext) (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) : sym_state * list sprep :=
  let lis := map (mk_sctx bc ex) (s_log ss) in
  let lia := map (fun e => EXF.sann_sp (mk_sctx bc ex e) e) (s_log ss) in
  let gl := EXF.GLof (mk_sctx bc ex) (s_log ss) in
  goL2 bc kn None ex t K fuel first stops (clr ss) lis lia gl (clr ss) lis lia gl wc_empty [] [] [] (EXF.mk_stt stops).
Lemma sym_execTXBIFL2_eq : forall bc kn ex t K fuel first stops ss,
  sym_execTXBIFL2 bc kn ex t K fuel first stops ss = EXF.sym_execTXBIFL segs bc kn ex t K fuel first stops ss.
Proof. intros. unfold sym_execTXBIFL2, EXF.sym_execTXBIFL. cbv zeta. apply goL2_eq; apply WCOK_empty. Qed.
Definition run_block_f2 (K : nat) (fuel : nat) (stops : list Z) (cs : acs) : option acs :=
  if BLKF.fresh_ok_f nx0 cs then
    let ss := a_ss cs in
    let bc := BLKF.mkbc_m (facts_of (s_know ss)) in
    let '(ss', scs) := sym_execTXBIFL2 bc (s_know ss) (mk_bext bc) IT K fuel true stops (SS (s_pc ss) (s_regs ss) [] (s_know ss) (s_next ss)) in
    match carryKF_ctx2 bc (s_log ss') scs (s_know ss') [] with
    | (kn', [], _) => Some (with_ss cs (mk_ss (s_pc ss') (s_regs ss') kn' (s_next ss')))
    | _ => None
    end
  else None.
Definition run_block_gc_f2 (K : nat) (fuel : nat) (stops : list Z) (cs : acs) : option acs :=
  match run_block_f2 K fuel stops cs with Some cs' => Some (BLKF.cs_gc_b nx0 cs') | None => None end.
Definition run_block_f3 (K : nat) (fuel : nat) (stops : list Z) (cs : acs) : option acs :=
  if BLKF.fresh_ok_f nx0 cs then
    let ss := a_ss cs in
    let bc := BLKF.mkbc_m (facts_of (s_know ss)) in
    let '(ss', scs) := sym_execTXBIFL2 bc (s_know ss) (mk_bext bc) IT K fuel true stops (SS (s_pc ss) (s_regs ss) [] (s_know ss) (s_next ss)) in
    match carryKF_ctx3 bc (s_log ss') scs (s_know ss') [] with
    | (kn', [], _) => Some (with_ss cs (mk_ss (s_pc ss') (s_regs ss') kn' (s_next ss')))
    | _ => None
    end
  else None.
Definition run_block_gc_f3 (K : nat) (fuel : nat) (stops : list Z) (cs : acs) : option acs :=
  match run_block_f3 K fuel stops cs with Some cs' => Some (BLKF.cs_gc_b nx0 cs') | None => None end.
End WithSegs.
Lemma run_block_gc_f2_eq : forall segs IT nx0 K fuel stops cs,
  run_block_gc_f2 segs IT nx0 K fuel stops cs = EXF.run_block_gc_f segs IT nx0 K fuel stops cs.
Proof.
  intros. unfold run_block_gc_f2, EXF.run_block_gc_f, run_block_f2, EXF.run_block_f.
  destruct (BLKF.fresh_ok_f nx0 cs); [|reflexivity]. cbv zeta. rewrite sym_execTXBIFL2_eq.
  destruct (EXF.sym_execTXBIFL _ _ _ _ _ _ _ _ _ _) as [ss' scs]. rewrite carryKF_ctx2_eq. reflexivity.
Qed.
Lemma run_block_gc_f2_fe : run_block_gc_f2 = EXF.run_block_gc_f.
Proof. fe. apply run_block_gc_f2_eq. Qed.
Lemma run_block_gc_f3_eq : forall segs IT nx0 K fuel stops cs,
  run_block_gc_f3 segs IT nx0 K fuel stops cs = EXF.run_block_gc_f segs IT nx0 K fuel stops cs.
Proof.
  intros. unfold run_block_gc_f3, EXF.run_block_gc_f, run_block_f3, EXF.run_block_f.
  destruct (BLKF.fresh_ok_f nx0 cs); [|reflexivity]. cbv zeta. rewrite sym_execTXBIFL2_eq, EXF.sym_execTXBIFL_eq.
  rewrite BLKF.mkbc_m_eq, BLKF.mk_kix_f_eq.
  rewrite EXF.sym_execTXBIF_eq by (first [reflexivity | eexists; reflexivity]).
  rewrite carryKF_ctx3_eq. reflexivity.
Qed.
Lemma run_block_gc_f3_fe : run_block_gc_f3 = EXF.run_block_gc_f.
Proof. fe. apply run_block_gc_f3_eq. Qed.
End CAR2.
