(* [comment removed for export] *)


From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_ikit Zh_kit Z_infl_iface Z_itab_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg ZIface InflateState Inftrees ItableModel RefInflateSafeTY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib.Step.simpl_sizes ::=
  try match goal with |- context [length (_ ++ _)] => rewrite !length_app end;
  cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
  rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1;
  try match goal with |- context [length (_ ++ _)] => rewrite !length_app end; cbn [length].

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PC_IT_CNT : Z := 0x1f260.      (* [comment removed for export] *)
Definition PC_IT_CNTX : Z := 0x1f280.     (* [comment removed for export] *)
Definition PC_IT_MAX0 : Z := 0x1f294.     (* [comment removed for export] *)
Definition PC_IT_MAXJ : Z := 0x1f398.     (* [comment removed for export] *)
Definition PC_IT_MINL : Z := 0x1f3b0.     (* [comment removed for export] *)
Definition PC_IT_MINJ : Z := 0x1f3cc.     (* [comment removed for export] *)
Definition PC_IT_KRAFT : Z := 0x1f3d4.    (* [comment removed for export] *)
Definition PC_IT_MAX1 : Z := 0x1f8b4.     (* [comment removed for export] *)
Definition PC_IT_OFFS : Z := 0x1f4dc.     (* [comment removed for export] *)
Definition PC_IT_SORT : Z := 0x1f574.     (* [comment removed for export] *)
Definition PC_IT_SORTN : Z := 0x1f568.    (* [comment removed for export] *)
Definition PC_IT_TYPE : Z := 0x1f5a0.     (* [comment removed for export] *)
Definition PC_IT_INIT : Z := 0x1f63c.     (* [comment removed for export] *)
Definition PC_IT_SUBJ : Z := 0x1f668.     (* [comment removed for export] *)
Definition PC_IT_TRIP : Z := 0x1f670.     (* [comment removed for export] *)
Definition PC_IT_FILL : Z := 0x1f6d0.     (* [comment removed for export] *)
Definition PC_IT_INCR : Z := 0x1f700.     (* [comment removed for export] *)
Definition PC_IT_NEXT : Z := 0x1f778.     (* [comment removed for export] *)
Definition PC_IT_SUB : Z := 0x1f784.      (* [comment removed for export] *)
Definition PC_IT_LEFT : Z := 0x1f7a4.     (* [comment removed for export] *)
Definition PC_IT_USED : Z := 0x1f7d4.     (* [comment removed for export] *)
Definition PC_IT_DONE : Z := 0x1f838.     (* [comment removed for export] *)
Definition PC_IT_TAIL : Z := 0x1f86c.     (* [comment removed for export] *)
Definition PC_IT_EPI : Z := 0x1f874.      (* [comment removed for export] *)
Definition PC_IT_NOSYM : Z := 0x1f8d8.    (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Record itx : Type := mkITX {
  tx_L : ilay; tx_s : inflate_state; tx_ty : codetype; tx_dsel : bool; tx_lofs : Z; tx_codes : Z; tx_lo : Z; tx_m0 : mem;
  tx_sp : word; tx_ra : word; tx_gp : word; tx_tp : word;
  tx_s0 : word; tx_s1 : word; tx_s2 : word; tx_s3 : word; tx_s4 : word; tx_s5 : word;
  tx_s6 : word; tx_s7 : word; tx_s8 : word; tx_s9 : word; tx_s10 : word; tx_s11 : word;
  tx_F : bvmap 5 word; tx_fc : bv 32
}.

Definition tx_W (X : itx) : list ivl :=
  [(tx_lo X, bv_unsigned (tx_sp X)); (il_As (tx_L X), il_As (tx_L X) + ZI_SIZE)].
(* [comment removed for export] *)
Definition tx_W1 (X : itx) : list ivl :=
  [(tx_lo X, bv_unsigned (tx_sp X)); (il_As (tx_L X) + 808, il_As (tx_L X) + 7160)].

Lemma tx_W1_sub : forall X, sub_fp (tx_W1 X) (tx_W X).
Proof.
  intros X x. unfold tx_W1, tx_W. cbn [outside inside fst snd]. intros H. lia.
Qed.

Definition it_saved (X : itx) : list cell :=
  [C8 (tx_s11 X); C8 (tx_s10 X); C8 (tx_s9 X); C8 (tx_s8 X); C8 (tx_s7 X); C8 (tx_s6 X); C8 (tx_s5 X); C8 (tx_s4 X);
   C8 (tx_s3 X); C8 (tx_s2 X); C8 (tx_s1 X); C8 (tx_s0 X); C8 (tx_ra X)].

(* [comment removed for export] *)
Definition tx_lens (X : itx) : arr := is_lens (tx_s X).
Definition tx_bits (X : itx) : Z := it_bits_get (tx_dsel X) (tx_s X).
Definition tx_table (X : itx) : Z := is_next (tx_s X).
(* [comment removed for export] *)
Definition tx_lensA (X : itx) : Z := il_As (tx_L X) + 168 + 2 * tx_lofs X.
Definition tx_bitsA (X : itx) : Z := il_As (tx_L X) + (if tx_dsel X then 140 else 136).

(* [comment removed for export] *)
Record itx_ok (X : itx) : Prop := mkITXok {
  xo_lo : tx_lo X <= bv_unsigned (tx_sp X) - Z_ITABLE_STACK;
  xo_As : 0 < il_As (tx_L X) /\ il_As (tx_L X) + ZI_SIZE <= tx_lo X /\ il_As (tx_L X) + ZI_SIZE < 2^62;
  xo_win : is_window_blk (tx_s X) <> None -> il_Aw (tx_L X) + ZI_WIN <= tx_lo X;
  xo_codes : 0 <= tx_lofs X /\ 0 <= tx_codes X /\ tx_lofs X + tx_codes X <= 320;
  xo_arrs : iarrs (tx_s X);
  xo_lay : ilay_ok (tx_L X) (tx_s X)
}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition itab_post (X : itx) : machine_state -> Prop :=
  inflate_table_post (tx_ra X) (tx_sp X) (tx_gp X) (tx_tp X) (tx_s0 X) (tx_s1 X) (tx_s2 X) (tx_s3 X) (tx_s4 X) (tx_s5 X) (tx_s6 X)
    (tx_s7 X) (tx_s8 X) (tx_s9 X) (tx_s10 X) (tx_s11 X) (tx_F X) (tx_fc X) (tx_L X) (tx_s X) (tx_ty X) (tx_dsel X) (tx_lofs X)
    (tx_codes X) (tx_lo X) (tx_m0 X).

(* [comment removed for export] *)
Definition it_res_state (s : inflate_state) (dsel : bool) (tb : arr) (nxt bts : Z) (wk : arr) : inflate_state :=
  iset_work (it_bits_set dsel (iset_next (iset_codes s tb) nxt) bts) wk.

(* [comment removed for export] *)
Definition tx_call (X : itx) : Z * arr * Z * Z * arr :=
  inflate_table (tx_ty X) (tx_lens X) (tx_lofs X) (tx_codes X) (is_codes (tx_s X)) (tx_table X) (tx_bits X) (is_work (tx_s X)).

Lemma it_result_eq : forall X ret tb nxt bts wk, tx_call X = (ret, tb, nxt, bts, wk) ->
  it_result (tx_ty X) (tx_dsel X) (tx_lofs X) (tx_codes X) (tx_s X) = (ret, it_res_state (tx_s X) (tx_dsel X) tb nxt bts wk).
Proof. intros X ret tb nxt bts wk H. unfold it_result. unfold tx_call, tx_lens, tx_table, tx_bits in H. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Record ITM (X : itx) (low : list cell) (cnt ofs wk tb : arr) (m : mem) : Prop := mkITM {
  tm_low : rw_cells psegs m (bv_unsigned (tx_sp X) + -192) low;
  tm_ofs : u8arr psegs m (bv_unsigned (tx_sp X) + -166) (u16s (av16s ofs 1 15));
  tm_cnt : u8arr psegs m (bv_unsigned (tx_sp X) + -136) (u16s (av16 cnt 16));
  tm_sav : rw_cells psegs m (bv_unsigned (tx_sp X) + -104) (it_saved X);
  tm_stk : stk psegs m (tx_lo X) (bv_unsigned (tx_sp X) + -192);
  tm_work : u16arr psegs m (il_As (tx_L X) + 808) (av16 wk 288);
  tm_codes : u32arr psegs m (il_As (tx_L X) + 1384) (av32 tb 1444);
  tm_mi : mem_inv psegs m;
  tm_mu : munch (tx_W1 X) (tx_m0 X) m;
  tm_wm : wmono psegs (tx_m0 X) m
}.

(* [comment removed for export] *)
Lemma ITM_isA : forall X low cnt ofs wk tb m, itx_ok X -> IST (tx_m0 X) (tx_L X) (tx_s X) -> ITM X low cnt ofs wk tb m -> isA m (tx_L X) (tx_s X).
Proof.
  intros X low cnt ofs wk tb m XO ST TM. apply (isA_munch (tx_m0 X) m _ _ (tx_W1 X)); [exact (ist_A _ _ _ ST)| exact (tm_mu _ _ _ _ _ _ _ TM)| exact (tm_wm _ _ _ _ _ _ _ TM)|].
  pose proof (xo_As X XO) as HA. unfold tx_W1. cbn [disjoint_from]. split; [lia| split; [lia| exact I]].
Qed.
Lemma ITM_isT : forall X low cnt ofs wk tb m, itx_ok X -> IST (tx_m0 X) (tx_L X) (tx_s X) -> ITM X low cnt ofs wk tb m -> isT m (tx_L X) (tx_s X).
Proof.
  intros X low cnt ofs wk tb m XO ST TM. apply (isT_munch (tx_m0 X) m _ _ (tx_W1 X)); [exact (ist_T _ _ _ ST)| exact (tm_mu _ _ _ _ _ _ _ TM)| exact (tm_wm _ _ _ _ _ _ _ TM)|].
  pose proof (xo_As X XO) as HA. unfold tx_W1. cbn [disjoint_from]. split; [lia| split; [lia| exact I]].
Qed.
Lemma ITM_ilens : forall X low cnt ofs wk tb m, itx_ok X -> IST (tx_m0 X) (tx_L X) (tx_s X) -> ITM X low cnt ofs wk tb m -> ilens m (tx_L X) (tx_s X).
Proof.
  intros X low cnt ofs wk tb m XO ST TM. apply (ilens_munch (tx_m0 X) m _ _ (tx_W1 X)); [exact (ist_lens _ _ _ ST)| exact (tm_mu _ _ _ _ _ _ _ TM)| exact (tm_wm _ _ _ _ _ _ _ TM)|].
  pose proof (xo_As X XO) as HA. unfold tx_W1. cbn [disjoint_from]. split; [lia| split; [lia| exact I]].
Qed.
Lemma ITM_iwin : forall X low cnt ofs wk tb m, itx_ok X -> IST (tx_m0 X) (tx_L X) (tx_s X) -> ITM X low cnt ofs wk tb m -> iwin m (tx_L X) (tx_s X).
Proof.
  intros X low cnt ofs wk tb m XO ST TM. apply (iwin_munch (tx_m0 X) m _ _ (tx_W1 X)); [exact (ist_win _ _ _ ST)| exact (tm_mu _ _ _ _ _ _ _ TM)| exact (tm_wm _ _ _ _ _ _ _ TM)|].
  intros NE. pose proof (xo_win X XO NE) as W1. destruct (ist_lay _ _ _ ST) as [_ LW]. destruct (LW NE) as [_ AP].
  pose proof (xo_As X XO) as HA. unfold apart in AP. unfold tx_W1. cbn [disjoint_from]. split; [lia| split; [lia| exact I]].
Qed.

(* [comment removed for export] *)
Lemma IST_result : forall X m tb nxt bts wk,
  itx_ok X -> isA m (tx_L X) (it_res_state (tx_s X) (tx_dsel X) tb nxt bts wk) ->
  isT m (tx_L X) (tx_s X) -> ilens m (tx_L X) (tx_s X) ->
  u16arr psegs m (il_As (tx_L X) + 808) (av16 wk 288) -> u32arr psegs m (il_As (tx_L X) + 1384) (av32 tb 1444) ->
  iwin m (tx_L X) (tx_s X) -> arr_len wk = 288 -> arr_len tb = 1444 ->
  IST m (tx_L X) (it_res_state (tx_s X) (tx_dsel X) tb nxt bts wk).
Proof.
  intros X m tb nxt bts wk XO GA GT Gl Gw Gc Gwin LW LT. destruct XO as [_ _ _ _ ARRS LAY].
  unfold it_res_state, it_bits_set in *. destruct (tx_dsel X).
  - constructor; [exact GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| | exact LAY].
    unfold iarrs in *. ired. tauto.
  - constructor; [exact GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| | exact LAY].
    unfold iarrs in *. ired. tauto.
Qed.

(* [comment removed for export] *)
Lemma isA_result_same : forall X m tb wk, isA m (tx_L X) (tx_s X) ->
  isA m (tx_L X) (it_res_state (tx_s X) (tx_dsel X) tb (tx_table X) (tx_bits X) wk).
Proof.
  intros X m tb wk GA. unfold it_res_state, it_bits_set, tx_bits, tx_table, it_bits_get. destruct (tx_dsel X); exact GA.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma itab_epilogue : forall X ret s' (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (m : mem) (j : list byte),
  itx_ok X ->
  rw_cells psegs m (bv_unsigned (tx_sp X) + -192) (CB 88 j :: it_saved X) ->
  stk psegs m (tx_lo X) (bv_unsigned (tx_sp X) + -192) ->
  IST m (tx_L X) s' -> mem_inv psegs m -> munch (tx_W X) (tx_m0 X) m -> wmono psegs (tx_m0 X) m ->
  it_result (tx_ty X) (tx_dsel X) (tx_lofs X) (tx_codes X) (tx_s X) = (ret, s') ->
  evt psegs (itab_post X)
    (MS (mkR x1 (wz (bv_unsigned (tx_sp X) + -192)) (tx_gp X) (tx_tp X) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 (wz ret) x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) (tx_F X) (wz PC_IT_EPI) (tx_fc X) None m (seg_rom psegs)).
Proof.
  intros until j. intros XO FR ST HIST MI MU WM ER.
  destruct XO as [XLO _ _ _ _ _]. unfold Z_ITABLE_STACK in XLO. unfold it_saved in FR. unfold tx_W in MU.
  unfold PC_IT_EPI. do 15 zs.
  release_frame FR ST (bv_unsigned (tx_sp X)). zs.
  apply evt_done. unfold itab_post, inflate_table_post. rewrite ER. cbn [fst snd].
  do 16 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [|exact HIST].
  symmetry. apply Z_to_bv_mod64.
Qed.

