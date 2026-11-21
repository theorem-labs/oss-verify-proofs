(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import PropExec CatExec SeqExec StoreOk Hoare.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import MemRel SymAux.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import ISLayout.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import ZIface InflateState InflateFast.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import InffastModel InflMem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Set Implicit Arguments.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.
Record iff_pre (segs : list Segment) (LFX DFX RLO RHI WLO : Z)
       (mem : word -> option byte) (sp : Z) (ra : word)
       (s : inflate_state) (c : icall) (r : iregs)
       (ZP S I0 P0 WB : Z) : Prop := IFP {
  ifp_ret : ret_ok ra;
  ifp_zs_in : cell segs mem (ZP + 0) 8 (I0 + ic_next_in c);
  ifp_zs_ain : cell segs mem (ZP + 8) 4 (ic_avail_in c);
  ifp_zs_out : cell segs mem (ZP + 24) 8 (P0 + ic_next_out c);
  ifp_zs_aout : cell segs mem (ZP + 32) 4 (ic_avail_out c);
  ifp_zs_state : cell segs mem (ZP + 56) 8 S;
  ifp_scalars : isl_scalars segs LFX DFX mem S (ISP ZP WB) s;
  ifp_codes : cells segs mem (S + 1384) 4 4 1444 (arr_get (is_codes s));
  ifp_codes_b : forall i, 0 <= i < 1444 -> 0 <= arr_get (is_codes s) i < 2 ^ 32;
  ifp_win : cells segs mem WB 1 1 (arr_len (is_window s)) (arr_get (is_window s));
  ifp_win_b : forall i, 0 <= i < arr_len (is_window s) -> 0 <= arr_get (is_window s) i < 256;
  ifp_in : cells segs mem I0 1 1 (arr_len (ic_input c)) (arr_get (ic_input c));
  ifp_in_b : forall i, 0 <= i < arr_len (ic_input c) -> 0 <= arr_get (ic_input c) i < 256;
  ifp_out : cells segs mem P0 1 1 (arr_len (ic_outbuf c)) (arr_get (ic_outbuf c));
  ifp_out_b : forall i, 0 <= i < arr_len (ic_outbuf c) -> 0 <= arr_get (ic_outbuf c) i < 256;
  ifp_rod : forall x : word, RLO <= bv_unsigned x < RHI -> mem x = None;
  ifp_RO : 0 <= RLO /\ RLO <= DFX /\ DFX + 128 <= RHI /\ RLO <= LFX /\ LFX + 2048 <= RHI /\ RHI <= WLO;
  ifp_sp : WLO <= sp /\ sp + 112 < 2 ^ 63;
  ifp_ZP : 0 < ZP /\ ZP + 112 < 2 ^ 63;
  ifp_S : 0 < S /\ S + 7176 < 2 ^ 63;
  ifp_I0 : 0 <= I0 /\ I0 + arr_len (ic_input c) < 2 ^ 63;
  ifp_P0 : 0 < P0 /\ P0 + arr_len (ic_outbuf c) < 2 ^ 63;
  ifp_WB : 0 <= WB /\ 0 <= arr_len (is_window s) /\ WB + arr_len (is_window s) < 2 ^ 63;
  ifp_o_Z : ZP + 112 <= RLO \/ WLO <= ZP;
  ifp_o_S : S + 7176 <= RLO \/ WLO <= S;
  ifp_o_P : 0 < arr_len (ic_outbuf c) -> P0 + arr_len (ic_outbuf c) <= RLO \/ WLO <= P0;
  ifp_d_spZ : sep sp 112 ZP 112;
  ifp_d_spS : sep sp 112 S 7176;
  ifp_d_spI : sep sp 112 I0 (arr_len (ic_input c));
  ifp_d_spP : sep sp 112 P0 (arr_len (ic_outbuf c));
  ifp_d_spW : sep sp 112 WB (arr_len (is_window s));
  ifp_d_PZ : sep P0 (arr_len (ic_outbuf c)) ZP 112;
  ifp_d_PS : sep P0 (arr_len (ic_outbuf c)) S 7176;
  ifp_d_PI : sep P0 (arr_len (ic_outbuf c)) I0 (arr_len (ic_input c));
  ifp_d_PW : sep P0 (arr_len (ic_outbuf c)) WB (arr_len (is_window s));
  ifp_d_ZS : sep ZP 112 S 7176;
  ifp_d_ZI : sep ZP 112 I0 (arr_len (ic_input c));
  ifp_d_ZW : sep ZP 112 WB (arr_len (is_window s));
  ifp_d_SI : sep S 7176 I0 (arr_len (ic_input c));
  ifp_d_SW : sep S 7176 WB (arr_len (is_window s));
  ifp_map_sp : mapped mem sp 112;
  ifp_map_P : mapped mem P0 (arr_len (ic_outbuf c));
  ifp_map_Z : mapped mem ZP 112;
  ifp_map_S : mapped mem S 7176;
  ifp_r_in : 0 <= ic_next_in c <= arr_len (ic_input c) /\ 0 <= ic_avail_in c < 2 ^ 32;
  ifp_r_out : 0 <= ic_next_out c /\ 0 <= ic_avail_out c /\ ic_next_out c + ic_avail_out c <= arr_len (ic_outbuf c);
  ifp_r_start : 0 <= ir_out r - ic_avail_out c <= ic_next_out c;
  ifp_r_room : arr_len (ic_outbuf c) < 2 ^ 32;
  ifp_r_hold : 0 <= is_hold s < 2 ^ is_bits s;
  ifp_r_bits : 0 <= is_bits s < 64;
  ifp_r_w : 0 <= is_wsize s < 2 ^ 31 /\ 0 <= is_whave s < 2 ^ 31 /\ 0 <= is_wnext s < 2 ^ 31;
  ifp_r_lb : 0 <= is_lenbits s <= 15 /\ 0 <= is_distbits s <= 15;
  ifp_r_sane : 0 <= is_sane s < 2 ^ 31;
  ifp_r_lencode : match is_lencode s with CDyn ofs => 0 <= ofs <= 1444 | _ => True end;
  ifp_r_distcode : match is_distcode s with CDyn ofs => 0 <= ofs <= 1444 | _ => True end
}.
End FXG.
Unset Implicit Arguments.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.



Definition ffx_of (s : inflate_state) (c : icall) (r : iregs) : ffx :=
  mkFX (ic_input c) (ic_next_in c + wrap32 (ic_avail_in c - 5))
       (ic_next_out c - wrap32 (ir_out r - ic_avail_out c))
       (ic_next_out c + wrap32 (ic_avail_out c - 257))
       (is_wsize s) (is_whave s) (is_wnext s) (is_window s)
       (zmask (is_lenbits s)) (zmask (is_distbits s)) (is_sane s).
Definition ff0_of (s : inflate_state) (c : icall) : ffs :=
  mkF (ic_next_in c) (ic_next_out c) (is_hold s) (is_bits s) 0 0 0 (FOut 0) (ic_outbuf c).

Definition ctab_len (p : codeptr) : Z :=
  match p with CDyn ofs => 1444 - ofs | CLenfix => 512 | CDistfix => 32 end.

Definition x_begm (c : icall) (r : iregs) : Z := ic_next_out c - szwrap 32 (ir_out r - ic_avail_out c).

Definition KREGS (sp ZP S I0 P0 WB : Z) (x : ffx) (bm LC DC : Z) (regs : bvmap 5 word) : Prop :=
  getr regs 2 = zw sp /\ getr regs 10 = zw ZP /\ getr regs 6 = zw S /\ getr regs 16 = zw LC /\ getr regs 7 = zw DC
  /\ getr regs 5 = zw (x_lmask x) /\ getr regs 22 = zw (x_dmask x)
  /\ getr regs 28 = zw (I0 + x_last x) /\ getr regs 29 = zw (P0 + x_end x) /\ getr regs 24 = zw (P0 + bm)
  /\ getr regs 26 = zw (x_wsize x) /\ getr regs 25 = zw (x_whave x) /\ getr regs 9 = zw (x_wnext x)
  /\ getr regs 23 = zw WB /\ getr regs 12 = zw 1 /\ getr regs 8 = zw 14.




Definition faddr (WB P0 : Z) (fr : fromptr) : Z := match fr with FWin i => WB + i | FOut i => P0 + i end.
Definition src_ok (WN bnd : Z) (fr : fromptr) : Prop := match fr with FWin i => 0 <= i < WN | FOut i => 0 <= i < bnd end.

Lemma faddr_succ : forall WB P0 fr, faddr WB P0 (from_succ fr) = faddr WB P0 fr + 1.
Proof. intros WB P0 [i|i]; cbn; lia. Qed.
Lemma faddr_add : forall WB P0 k fr, faddr WB P0 (fr_add fr k) = faddr WB P0 fr + Z.of_nat k.
Proof.
  intros WB P0 k. induction k as [|k IH]; intros fr; [cbn; lia|].
  cbn [fr_add]. rewrite IH, faddr_succ. lia.
Qed.
Lemma src_ok_weaken : forall WN b b' fr, src_ok WN b fr -> b <= b' -> src_ok WN b' fr.
Proof. intros WN b b' [i|i] H Hb; cbn in *; lia. Qed.

Definition FF0 (sp : Z) : franges := [(sp, 112)].
Definition FF1 (sp P0 ON : Z) : franges := [(sp, 112); (P0, ON)].
Definition FFall (sp P0 ON ZP S : Z) : franges :=
  [(sp, 112); (P0, ON); (ZP, 12); (ZP + 24, 12); (ZP + 48, 8); (S + 8, 4); (S + 96, 12)].

Definition FINV (mem : word -> option byte) (sp P0 ON ZP S : Z)
           (F : franges) (m : word -> option byte) : Prop :=
  agree_out F mem m
  /\ mapped m sp 112 /\ mapped m P0 ON /\ mapped m ZP 112 /\ mapped m S 7176
  /\ (forall x, mem x <> None -> m x <> None).


Definition SVok (SV : list (Z * nat * Z)) : Prop := forall e, In e SV -> let '(o, w, _) := e in 0 <= o /\ o + Z.of_nat w <= 112.


Definition MEMINV (segs : list Segment) (mem : word -> option byte) (sp ON ZP S P0 : Z)
           (SV : list (Z * nat * Z)) (m : word -> option byte) (ob : arr) : Prop :=
  FINV mem sp P0 ON ZP S (FF1 sp P0 ON) m
  /\ fcells segs sp m SV /\ SVok SV
  /\ cells segs m P0 1 1 ON (arr_get ob)
  /\ arr_len ob = ON
  /\ (forall i, 0 <= i < ON -> 0 <= arr_get ob i < 256).

Section Facts.
Context {segs : list Segment} {LFX DFX RLO RHI WLO : Z}
        {mem : word -> option byte} {sp : Z} {ra : word}
        {s : inflate_state} {c : icall} {r : iregs}
        {ZP S I0 P0 WB : Z}.
Variable C : iff_pre segs LFX DFX RLO RHI WLO mem sp ra s c r ZP S I0 P0 WB.
Local Notation IN := (arr_len (ic_input c)).
Local Notation ON := (arr_len (ic_outbuf c)).
Local Notation WN := (arr_len (is_window s)).
Local Notation LF := (FFall sp P0 (arr_len (ic_outbuf c)) ZP S).
Local Notation LF1 := (FF1 sp P0 (arr_len (ic_outbuf c))).
Local Notation FI := (FINV mem sp P0 (arr_len (ic_outbuf c)) ZP S).

Lemma FF0_FF1 : forall x, in_franges (FF0 sp) x -> in_franges LF1 x.
Proof. unfold FF0, FF1. cbn [in_franges]. intros x Hx. tauto. Qed.
Lemma FF1_FF : forall x, in_franges LF1 x -> in_franges LF x.
Proof. unfold FF1, FFall. cbn [in_franges]. intros x Hx. tauto. Qed.

Lemma FINV_weaken : forall F G m, FI F m -> (forall x, in_franges F x -> in_franges G x) -> FI G m.
Proof. intros F G m (Hag & Hr) HFG. split; [exact (agree_out_weaken F G mem m Hag HFG) | exact Hr]. Qed.
Lemma FINV_agree : forall F m, FI F m -> agree_out F mem m.
Proof. intros F m (H & _). exact H. Qed.
Lemma FINV_map_sp : forall F m, FI F m -> forall x : word, sp <= bv_unsigned x < sp + 112 -> m x <> None.
Proof. intros F m (_ & H & _). exact H. Qed.
Lemma FINV_map_P : forall F m, FI F m -> forall x : word, P0 <= bv_unsigned x < P0 + ON -> m x <> None.
Proof. intros F m (_ & _ & H & _). exact H. Qed.
Lemma FINV_map_Z : forall F m, FI F m -> forall x : word, ZP <= bv_unsigned x < ZP + 112 -> m x <> None.
Proof. intros F m (_ & _ & _ & H & _). exact H. Qed.
Lemma FINV_map_S : forall F m, FI F m -> forall x : word, S <= bv_unsigned x < S + 7176 -> m x <> None.
Proof. intros F m (_ & _ & _ & _ & H & _). exact H. Qed.
Lemma FINV_grows : forall F m, FI F m -> forall x, mem x <> None -> m x <> None.
Proof. intros F m (_ & _ & _ & _ & _ & H). exact H. Qed.


Lemma FINV_init : FI (FF0 sp) mem.
Proof.
  unfold FINV. split; [apply agree_out_refl|].
  split; [exact (ifp_map_sp C)|]. split; [exact (ifp_map_P C)|]. split; [exact (ifp_map_Z C)|].
  split; [exact (ifp_map_S C)|]. intros x Hx; exact Hx.
Qed.

Lemma FINV1_win : forall m, FI LF1 m -> cells segs m WB 1 1 WN (arr_get (is_window s)).
Proof.
  intros m (Hag & _).
  pose proof (ifp_RO C). pose proof (ifp_sp C). pose proof (ifp_WB C). pose proof (ifp_P0 C).
  pose proof (ifp_d_spW C). pose proof (ifp_d_PW C).
  refine (cells_agree_out segs LF1 mem m WB 1 1 WN _ Hag _ _ _ _ (ifp_win C)); try lia.
  unfold FF1. repeat (apply disj_franges_cons; [sep_solve|]). apply disj_franges_nil.
Qed.
Lemma FINV1_in : forall m, FI LF1 m -> cells segs m I0 1 1 IN (arr_get (ic_input c)).
Proof.
  intros m (Hag & _).
  pose proof (ifp_RO C). pose proof (ifp_sp C). pose proof (ifp_I0 C). pose proof (ifp_P0 C).
  pose proof (ifp_d_spI C). pose proof (ifp_d_PI C).
  refine (cells_agree_out segs LF1 mem m I0 1 1 IN _ Hag _ _ _ _ (ifp_in C)); try lia.
  unfold FF1. repeat (apply disj_franges_cons; [sep_solve|]). apply disj_franges_nil.
Qed.
Lemma FINV1_codes : forall m, FI LF1 m -> cells segs m (S + 1384) 4 4 1444 (arr_get (is_codes s)).
Proof.
  intros m (Hag & _).
  pose proof (ifp_RO C). pose proof (ifp_sp C). pose proof (ifp_S C). pose proof (ifp_P0 C).
  pose proof (ifp_d_spS C). pose proof (ifp_d_PS C).
  refine (cells_agree_out segs LF1 mem m (S + 1384) 4 4 1444 _ Hag _ _ _ _ (ifp_codes C)); try lia.
  unfold FF1. repeat (apply disj_franges_cons; [sep_solve|]). apply disj_franges_nil.
Qed.
Lemma FINV1_scalars : forall m, FI LF1 m -> isl_scalars segs LFX DFX m S (ISP ZP WB) s.
Proof.
  intros m (Hag & _).
  pose proof (ifp_RO C). pose proof (ifp_sp C). pose proof (ifp_S C). pose proof (ifp_P0 C).
  pose proof (ifp_d_spS C). pose proof (ifp_d_PS C).
  refine (fields_agree_out segs LF1 mem m S isl_layout _ isl_SIZE (ifp_scalars C) isl_layout_within Hag _ _ _); try (unfold isl_SIZE; lia).
  unfold FF1, isl_SIZE. repeat (apply disj_franges_cons; [sep_solve|]). apply disj_franges_nil.
Qed.
Lemma FINV1_rod : forall m, FI LF1 m -> forall x : word, RLO <= bv_unsigned x < RHI -> m x = None.
Proof.
  intros m (Hag & _) x Hx.
  pose proof (ifp_RO C). pose proof (ifp_sp C). pose proof (ifp_P0 C). pose proof (ifp_o_P C).
  rewrite (Hag x); [exact (ifp_rod C x Hx)|].
  unfold FF1. cbn [in_franges]. lia.
Qed.

Lemma FINV_store : forall F m (b : Z) bs,
  FI F m -> 0 <= b -> b + Z.of_nat (length bs) <= 2 ^ 64 -> sub_franges F b (Z.of_nat (length bs)) ->
  FI F (wbytes m (zw b) bs).
Proof.
  intros F m b bs (Hag & M1 & M2 & M3 & M4 & Hgr) Hb0 Hb1 Hsub. unfold FINV.
  split; [apply agree_out_wbytes; assumption|].
  split; [apply mapped_wbytes; exact M1|]. split; [apply mapped_wbytes; exact M2|].
  split; [apply mapped_wbytes; exact M3|]. split; [apply mapped_wbytes; exact M4|].
  intros x Hx. apply wbytes_grows. exact (Hgr x Hx).
Qed.

Lemma FINV_store_sp : forall F' m (o : Z) (w : nat) v,
  FI ((sp, 112) :: F') m -> 0 <= o -> o + Z.of_nat w <= 112 ->
  FI ((sp, 112) :: F') (wbytes m (zw (sp + o)) (Z_to_le_bytes w v)).
Proof.
  intros F' m o w v HM Ho How. pose proof (ifp_RO C). pose proof (ifp_sp C).
  apply FINV_store; rewrite ?length_Z_to_le_bytes; try lia; [exact HM|].
  apply sub_franges_here; lia.
Qed.

Lemma FINV_store_out : forall F' m (i : Z) bs,
  FI ((sp, 112) :: (P0, ON) :: F') m -> 0 <= i -> i + Z.of_nat (length bs) <= ON ->
  FI ((sp, 112) :: (P0, ON) :: F') (wbytes m (zw (P0 + i)) bs).
Proof.
  intros F' m i bs HM Hi Hin. pose proof (ifp_RO C). pose proof (ifp_P0 C).
  apply FINV_store; try lia; [exact HM|].
  apply sub_franges_later, sub_franges_here; lia.
Qed.

Lemma out_store_sp : forall m f (o : Z) (w : nat) v,
  cells segs m P0 1 1 ON f -> 0 <= o -> o + Z.of_nat w <= 112 ->
  cells segs (wbytes m (zw (sp + o)) (Z_to_le_bytes w v)) P0 1 1 ON f.
Proof.
  intros m f o w v Hc Ho How.
  pose proof (ifp_RO C). pose proof (ifp_sp C). pose proof (ifp_P0 C). pose proof (ifp_d_spP C) as Hs.
  destruct (Z_lt_le_dec ON 0) as [Hneg|Hnn]; [intros j Hj; lia|].
  apply cells_write_other; rewrite ?length_Z_to_le_bytes; try (cbn; lia); [exact Hc|]. destruct Hs; [right | left]; lia.
Qed.
Lemma out_set1 : forall m (a : arr) (i : Z) v,
  cells segs m P0 1 1 ON (arr_get a) -> arr_len a = ON -> 0 <= i < ON ->
  cells segs (wbytes m (zw (P0 + i)) (Z_to_le_bytes 1 v)) P0 1 1 ON (arr_get (arr_set a i (wrap8 v))).
Proof.
  intros m a i v Hc HL Hi. pose proof (ifp_P0 C). pose proof (ifp_RO C).
  replace (P0 + i) with (P0 + 1 * i) by lia.
  apply (cells_ext_mod segs _ _ 1 1 ON (fun j => if Z.eqb j i then v else arr_get a j)).
  - apply cells_write_cell; [exact Hc | lia | lia | lia | lia].
  - intros j Hj. rewrite arr_get_set. change (2 ^ (8 * Z.of_nat 1)) with 256.
    destruct (Z.eqb_spec i j) as [->|Hne]; cbn [andb].
    + replace (arr_inb a j) with true by (symmetry; apply arr_inb_spec; lia). rewrite Z.eqb_refl.
      rewrite wrap8_mod. rewrite Z.mod_mod; lia.
    + replace (j =? i) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.

Lemma ffx_lmask_range : 0 <= x_lmask (ffx_of s c r) < 65536.
Proof.
  cbn [x_lmask ffx_of]. pose proof (ifp_r_lb C) as H. rewrite zmask_pow2 by lia.
  pose proof (pow2_le (is_lenbits s) 15 ltac:(lia)). pose proof (Z.pow_pos_nonneg 2 (is_lenbits s) ltac:(lia) ltac:(lia)).
  change (2 ^ 15) with 32768 in *. lia.
Qed.
Lemma ffx_dmask_range : 0 <= x_dmask (ffx_of s c r) < 65536.
Proof.
  cbn [x_dmask ffx_of]. pose proof (ifp_r_lb C) as H. rewrite zmask_pow2 by lia.
  pose proof (pow2_le (is_distbits s) 15 ltac:(lia)). pose proof (Z.pow_pos_nonneg 2 (is_distbits s) ltac:(lia) ltac:(lia)).
  change (2 ^ 15) with 32768 in *. lia.
Qed.
Lemma ffx_lmask_eq : x_lmask (ffx_of s c r) = 2 ^ is_lenbits s - 1.
Proof. cbn [x_lmask ffx_of]. pose proof (ifp_r_lb C). apply zmask_pow2. lia. Qed.
Lemma ffx_dmask_eq : x_dmask (ffx_of s c r) = 2 ^ is_distbits s - 1.
Proof. cbn [x_dmask ffx_of]. pose proof (ifp_r_lb C). apply zmask_pow2. lia. Qed.
Lemma ffx_last_range : 0 <= x_last (ffx_of s c r) <= IN + 2 ^ 32.
Proof.
  cbn [x_last ffx_of]. pose proof (ifp_r_in C). rewrite wrap32_mod.
  pose proof (Z.mod_pos_bound (ic_avail_in c - 5) (2 ^ 32) ltac:(lia)). lia.
Qed.
Lemma ffx_end_range : 0 <= x_end (ffx_of s c r) <= ON + 2 ^ 32.
Proof.
  cbn [x_end ffx_of]. pose proof (ifp_r_out C). rewrite wrap32_mod.
  pose proof (Z.mod_pos_bound (ic_avail_out c - 257) (2 ^ 32) ltac:(lia)). lia.
Qed.
Lemma ffx_beg_range : 0 <= x_beg (ffx_of s c r) <= ic_next_out c.
Proof.
  cbn [x_beg ffx_of]. pose proof (ifp_r_out C). pose proof (ifp_r_start C). pose proof (ifp_r_room C).
  rewrite wrap32_id by lia. lia.
Qed.
Lemma ffx_beg_eq : x_beg (ffx_of s c r) = ic_next_out c - (ir_out r - ic_avail_out c).
Proof.
  cbn [x_beg ffx_of]. pose proof (ifp_r_out C). pose proof (ifp_r_start C). pose proof (ifp_r_room C).
  rewrite wrap32_id by lia. lia.
Qed.

Lemma lc_bounds : 0 <= codeptr_addr LFX DFX S (is_lencode s) /\ 0 <= ctab_len (is_lencode s)
  /\ codeptr_addr LFX DFX S (is_lencode s) + 4 * ctab_len (is_lencode s) < 2 ^ 63.
Proof.
  pose proof (ifp_r_lencode C) as H. pose proof (ifp_RO C). pose proof (ifp_S C). pose proof (ifp_sp C).
  destruct (is_lencode s); cbn [codeptr_addr ctab_len] in *; lia.
Qed.
Lemma dc_bounds : 0 <= codeptr_addr LFX DFX S (is_distcode s) /\ 0 <= ctab_len (is_distcode s)
  /\ codeptr_addr LFX DFX S (is_distcode s) + 4 * ctab_len (is_distcode s) < 2 ^ 63.
Proof.
  pose proof (ifp_r_distcode C) as H. pose proof (ifp_RO C). pose proof (ifp_S C). pose proof (ifp_sp C).
  destruct (is_distcode s); cbn [codeptr_addr ctab_len] in *; lia.
Qed.
Lemma hold_lt64 : is_hold s < 2 ^ 64.
Proof.
  pose proof (ifp_r_hold C). pose proof (ifp_r_bits C).
  pose proof (pow2_le (is_bits s) 64 ltac:(lia)). lia.
Qed.
Lemma lenbits_pow : 1 <= 2 ^ is_lenbits s <= 32768.
Proof.
  pose proof (ifp_r_lb C). change 1 with (2 ^ 0). change 32768 with (2 ^ 15).
  split; apply Z.pow_le_mono_r; lia.
Qed.
Lemma distbits_pow : 1 <= 2 ^ is_distbits s <= 32768.
Proof.
  pose proof (ifp_r_lb C). change 1 with (2 ^ 0). change 32768 with (2 ^ 15).
  split; apply Z.pow_le_mono_r; lia.
Qed.

Lemma FINV1_ctab_dyn : forall m ofs, FI LF1 m -> 0 <= ofs <= 1444 ->
  cells segs m (codeptr_addr LFX DFX S (CDyn ofs)) 4 4 (ctab_len (CDyn ofs)) (code_at s (CDyn ofs)).
Proof.
  intros m ofs HM Hofs. cbn [codeptr_addr ctab_len code_at].
  pose proof (cells_shift segs m (S + 1384) 4 1444 (arr_get (is_codes s)) ofs (FINV1_codes m HM) Hofs) as H.
  exact H.
Qed.

Local Notation MI := (MEMINV segs mem sp (arr_len (ic_outbuf c)) ZP S P0).

Lemma MEMI_FINV : forall SV m ob, MI SV m ob -> FI LF1 m.
Proof. intros SV m ob (H & _). exact H. Qed.
Lemma MEMI_saved : forall SV m ob, MI SV m ob -> fcells segs sp m SV.
Proof. intros SV m ob (_ & H & _). exact H. Qed.
Lemma MEMI_out : forall SV m ob, MI SV m ob -> cells segs m P0 1 1 ON (arr_get ob).
Proof. intros SV m ob (_ & _ & _ & H & _). exact H. Qed.
Lemma MEMI_len : forall SV m ob, MI SV m ob -> arr_len ob = ON.
Proof. intros SV m ob (_ & _ & _ & _ & H & _). exact H. Qed.
Lemma MEMI_ob_b : forall SV m ob, MI SV m ob -> forall i, 0 <= i < ON -> 0 <= arr_get ob i < 256.
Proof. intros SV m ob (_ & _ & _ & _ & _ & H). exact H. Qed.
Lemma MEMI_win : forall SV m ob, MI SV m ob -> cells segs m WB 1 1 WN (arr_get (is_window s)).
Proof. intros SV m ob HM. exact (FINV1_win m (MEMI_FINV SV m ob HM)). Qed.
Lemma MEMI_in : forall SV m ob, MI SV m ob -> cells segs m I0 1 1 IN (arr_get (ic_input c)).
Proof. intros SV m ob HM. exact (FINV1_in m (MEMI_FINV SV m ob HM)). Qed.
Lemma MEMI_scalars : forall SV m ob, MI SV m ob -> isl_scalars segs LFX DFX m S (ISP ZP WB) s.
Proof. intros SV m ob HM. exact (FINV1_scalars m (MEMI_FINV SV m ob HM)). Qed.
Lemma MEMI_map_P : forall SV m ob, MI SV m ob -> forall x : word, P0 <= bv_unsigned x < P0 + ON -> m x <> None.
Proof. intros SV m ob HM. exact (FINV_map_P _ m (MEMI_FINV SV m ob HM)). Qed.

Lemma MEMI_store_out1 : forall SV m ob (i : Z) v,
  MI SV m ob -> 0 <= i < ON -> 0 <= wrap8 v < 256 ->
  MI SV (wbytes m (zw (P0 + i)) (Z_to_le_bytes 1 v)) (arr_set ob i (wrap8 v)).
Proof.
  intros SV m ob i v (HF & HS & HSV & HC & HL & HB) Hi Hv.
  pose proof (ifp_sp C). pose proof (ifp_P0 C). pose proof (ifp_RO C). pose proof (ifp_d_spP C).
  split; [apply (FINV_store_out _ m i); [exact HF | lia | rewrite length_Z_to_le_bytes; cbn; lia]|].
  split.
  { apply (fcells_store_far segs sp 112); rewrite ?length_Z_to_le_bytes; try (cbn; lia); [exact HS| |].
    - eapply sep_sub; [exact H2| lia | lia | lia | cbn; lia].
    - intros e He. pose proof (HSV e He) as HH. destruct e as [[o w] vv]. lia. }
  split; [exact HSV|].
  split; [apply (out_set1 m ob i v HC HL Hi)|].
  split; [rewrite arr_len_set; exact HL|].
  intros j Hj. rewrite arr_get_set. destruct (_ && _); [exact Hv | apply HB; exact Hj].
Qed.


Lemma faddr_range : forall bnd fr, src_ok WN bnd fr -> bnd <= ON -> 0 <= faddr WB P0 fr /\ faddr WB P0 fr + 1 < 2 ^ 63.
Proof.
  intros bnd [i|i] H Hb; cbn in *; pose proof (ifp_WB C); pose proof (ifp_P0 C); pose proof (ifp_RO C); lia.
Qed.
Lemma faddr_disj : forall fout fr, src_ok WN fout fr -> 0 <= fout < ON ->
  faddr WB P0 fr + 1 <= P0 + fout \/ P0 + fout + 1 <= faddr WB P0 fr.
Proof.
  intros fout [i|i] H Hf; cbn in *; [|left; lia].
  pose proof (ifp_d_PW C) as Hs. unfold sep in Hs. destruct Hs; [right | left]; lia.
Qed.
Lemma fval_byte : forall SV m ob bnd fr, MI SV m ob -> src_ok WN bnd fr -> bnd <= ON ->
  0 <= fval (is_window s) ob fr < 256.
Proof.
  intros SV m ob bnd [i|i] HM H Hb; cbn in *; [apply (ifp_win_b C); lia | apply (MEMI_ob_b SV m ob HM); lia].
Qed.
Lemma src_read : forall SV m ob bnd fr a, MI SV m ob -> src_ok WN bnd fr -> bnd <= ON -> a = faddr WB P0 fr ->
  exists bs, rdn segs m (zw a) 1 = Some bs /\ bytes_le_to_Z bs = fval (is_window s) ob fr.
Proof.
  intros SV m ob bnd fr a HM H Hb ->. pose proof (fval_byte SV m ob bnd fr HM H Hb) as Hv.
  destruct fr as [i|i]; cbn in *.
  - apply (bytes_read segs m WB WN _ i (MEMI_win SV m ob HM)); [lia | exact Hv].
  - apply (bytes_read segs m P0 ON _ i (MEMI_out SV m ob HM)); [lia | exact Hv].
Qed.
Lemma MEMI_cp1 : forall SV m ob (i : Z) v,
  MI SV m ob -> 0 <= i < ON -> 0 <= v < 256 ->
  MI SV (wbytes m (zw (P0 + i)) (Z_to_le_bytes 1 v)) (arr_set ob i v).
Proof.
  intros SV m ob i v HM Hi Hv. rewrite <- (wrap8_id v Hv) at 2.
  apply MEMI_store_out1; [exact HM | exact Hi | rewrite wrap8_id by exact Hv; exact Hv].
Qed.

End Facts.
End FXG.
