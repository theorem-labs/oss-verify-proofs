From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Contract KindBGlue Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require MState Mem Frame Exec Cells Step.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import PjStruct PjIn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import Ledger ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import PvDefs PvModel PvGlue.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require strtod_c.
Import ListNotations.
Local Open Scope Z_scope.
Module Frame := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.Frame.
Module MState := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.MState.
Module Exec := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.Exec.
Module Mem := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.Mem.

Lemma pvk_items : forall d, (d <= MAXD)%nat -> PARSE_VALUE_K d = PARSE_VALUE_F + Z.max PV_LEAF (PARSE_ITEMS_K d).
Proof.
  intros d Hd. unfold PARSE_VALUE_K, PARSE_ITEMS_K.
  destruct (Nat.ltb_spec d MAXD) as [H|H].
  - replace (MAXD - d)%nat with (S (MAXD - S d)) by (unfold MAXD in *; lia). reflexivity.
  - replace (MAXD - d)%nat with 0%nat by (unfold MAXD in *; lia). reflexivity.
Qed.

Lemma pv_leaf_val : PV_LEAF = 8928.
Proof. reflexivity. Qed.

Lemma pvk_bounds : forall d, (d <= MAXD)%nat ->
  64 + 8928 <= PARSE_VALUE_K d /\ PARSE_ITEMS_K d + 64 <= PARSE_VALUE_K d /\ 0 <= PARSE_ITEMS_K d.
Proof.
  intros d Hd. rewrite (pvk_items d Hd), pv_leaf_val. unfold PARSE_VALUE_F.
  assert (0 <= PARSE_ITEMS_K d).
  { unfold PARSE_ITEMS_K. destruct (d <? MAXD)%nat; [|unfold PARSE_ITEMS_F; lia].
    unfold PARSE_ITEMS_F, PI_LEAF. pose proof (Z.le_max_l GROW_K (Z.max PARSE_STRING_K FREE_K)).
    pose proof (Z.le_max_l (Z.max GROW_K (Z.max PARSE_STRING_K FREE_K)) (PARSE_VALUE_K (S d))).
    unfold GROW_K, GROW_F, REALLOC_K, REALLOC_STACK, ALLOC_STACK in *. lia. }
  lia.
Qed.

Lemma pv_consts : PARSE_STRING_K = 8352 /\ MALLOC_K = 8224 /\ LITERAL_K = 64 /\ strtod_c.STRTOD_K = 8928 /\
  ALLOC_STACK = 8192.
Proof. repeat split; reflexivity. Qed.

Lemma outside2 : forall a1 b1 a2 b2 x, ~ Frame.outside [(a1, b1); (a2, b2)] x -> a1 <= x < b1 \/ a2 <= x < b2.
Proof. intros a1 b1 a2 b2 x H. cbn [Frame.outside] in H. lia. Qed.

Lemma outside3 : forall a1 b1 a2 b2 a3 b3 x, ~ Frame.outside [(a1, b1); (a2, b2); (a3, b3)] x ->
  a1 <= x < b1 \/ a2 <= x < b2 \/ a3 <= x < b3.
Proof. intros a1 b1 a2 b2 a3 b3 x H. cbn [Frame.outside] in H. lia. Qed.

Lemma rsegs_len : length rsegs = 4%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma rsegs_in : forall s, In s rsegs -> 0x10000 <= Z.of_N (seg_base s) /\ Z.of_N (seg_base s) + Z.of_N (seg_size s) <= 0x55000 /\
  (seg_writable s = false -> Z.of_N (seg_base s) + Z.of_N (seg_size s) <= 0x22000).
Proof.
  intros s Hs.
  assert (C : forallb (fun s => (0x10000 <=? Z.of_N (seg_base s)) && (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0x55000) &&
                         (seg_writable s || (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0x22000))) rsegs = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in C. specialize (C s Hs).
  apply andb_prop in C as [C C3]. apply andb_prop in C as [C1 C2]. apply Z.leb_le in C1, C2.
  split; [lia|]. split; [lia|]. intros Hw. rewrite Hw in C3. cbn in C3. apply Z.leb_le in C3. exact C3.
Qed.

Lemma rres_map : map (fun s => (bv_unsigned (fst s), bv_unsigned (snd s))) (segments_reserved rsegs) =
  [(65536, 8192); (73728, 65536); (139264, 4096); (143360, 204800)].
Proof. vm_compute. reflexivity. Qed.

Section M.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable RF : ResForm.
Local Abbreviation segs := (ms_segs B).
Local Abbreviation MR := (aa_MR API).

Lemma img_iff : ms_segs B = rsegs -> forall a, in_img B a <-> 0x10000 <= a < 0x55000.
Proof.
  intros SEG a. unfold in_img. rewrite SEG. split.
  - intros (_ & s & Hs & Ha).
    assert (Hm : In (bv_unsigned (fst s), bv_unsigned (snd s))
                   (map (fun s => (bv_unsigned (fst s), bv_unsigned (snd s))) (segments_reserved rsegs)))
      by (apply in_map_iff; exists s; split; [reflexivity | exact Hs]).
    rewrite rres_map in Hm. cbn in Hm.
    destruct Hm as [E|[E|[E|[E|[]]]]]; injection E as E1 E2; rewrite <- E1, <- E2 in *; lia.
  - intros Ha. split; [intros H; pose proof rsegs_len as L; rewrite H in L; discriminate|].
    assert (Hp : exists lo len, In (lo, len) (map (fun s => (bv_unsigned (fst s), bv_unsigned (snd s))) (segments_reserved rsegs)) /\
                   lo <= a < lo + len).
    { rewrite rres_map. cbn [In].
      destruct (Z_lt_ge_dec a 73728); [exists 65536, 8192; split; [left; reflexivity | lia]|].
      destruct (Z_lt_ge_dec a 139264); [exists 73728, 65536; split; [right; left; reflexivity | lia]|].
      destruct (Z_lt_ge_dec a 143360); [exists 139264, 4096; split; [right; right; left; reflexivity | lia]|].
      exists 143360, 204800; split; [right; right; right; left; reflexivity | lia]. }
    destruct Hp as (lo & len & Hin & Hr). apply in_map_iff in Hin as (s & E & Hs). injection E as E1 E2.
    exists s. split; [exact Hs | lia].
Qed.

Lemma seg_img : ms_segs B = rsegs -> forall x s, find_segment segs x 1 = Some s -> 0x10000 <= x < 0x55000 /\
  (seg_writable s = false -> x < 0x22000).
Proof.
  intros SEG x s F. rewrite SEG in F. destruct (kb_find_segment rsegs x 1 s F) as (Hin & H1 & H2).
  destruct (rsegs_in s Hin) as (R1 & R2 & R3). split; [lia|]. intros Hw. specialize (R3 Hw). lia.
Qed.

Lemma ro_low : ms_segs B = rsegs -> forall x, Mem.ro_addr segs x = true -> 0x10000 <= bv_unsigned x < 0x22000.
Proof.
  intros SEG x H. unfold Mem.ro_addr in H.
  destruct (find_segment segs (bv_unsigned x) 1) as [s|] eqn:F; [|discriminate].
  apply negb_true_iff in H. destruct (seg_img SEG _ _ F) as [H1 H2]. specialize (H2 H). lia.
Qed.

Lemma not_img_ro : ms_segs B = rsegs -> forall a, 0 <= a < 2 ^ 64 -> ~ in_img B a ->
  Mem.ro_addr segs (Z_to_bv 64 a) = false.
Proof.
  intros SEG a Ha Hn. destruct (Mem.ro_addr segs (Z_to_bv 64 a)) eqn:E; [|reflexivity].
  exfalso. apply Hn. apply (img_iff SEG). pose proof (ro_low SEG _ E) as R.
  rewrite MState.unsigned_lit in R by exact Ha. lia.
Qed.

Lemma not_img_seg : ms_segs B = rsegs -> forall a, ~ in_img B a -> find_segment segs a 1 = None.
Proof.
  intros SEG a Hn. destruct (find_segment segs a 1) as [s|] eqn:F; [|reflexivity].
  exfalso. apply Hn. apply (img_iff SEG). exact (proj1 (seg_img SEG _ _ F)).
Qed.

Lemma pv_img_low : ms_segs B = rsegs -> img_low B.
Proof.
  intros SEG. apply (img_low_of_check B 0x55000).
  - unfold img_check. rewrite SEG. vm_compute. reflexivity.
  - pose proof alloc_ceiling_val. lia.
Qed.

Lemma ceil_big : 0x55000 < alloc_ceiling /\ alloc_ceiling < 2 ^ 47.
Proof. pose proof alloc_ceiling_val. pose proof alloc_ceiling_lt. lia. Qed.

Definition pv_pre (d : nat) L A regs mem md Lam peak cnt fail b q text len p tb v : Prop :=
  reader_env B API (PARSE_VALUE_K d) L A regs mem md /\
  ledger B L A mem Lam peak cnt fail /\
  rf_ok RF A b /\
  getr regs 10 = Z_to_bv 64 q /\ getr regs 11 = Z_to_bv 64 v /\
  pj_in_ok segs mem q text len p (Z.of_nat d) tb /\
  spZ regs <= q /\ (st_init_done A = false -> auxv_pre B (ly_sec L) (q + 24) mem) /\
  Z.of_nat (PjRoundTrip.maxrun (zb tb)) < 2 ^ 30 /\
  text_ok B L A Lam regs text len /\
  v <> 0 /\ pj_zero segs mem v /\ rplace B L A Lam regs mem v /\
  Frame.disjoint_from [(text, text + len); (q, q + 24)] v 56 /\
  Frame.disjoint_from [(q, q + 24); (text, text + len); (v, v + 56)]
    (spZ regs - PARSE_VALUE_K d) (PARSE_VALUE_K d) /\
  cnt + 2 * Z.of_nat (length (rest_at tb text p)) + 2 < 2 ^ 64 - 1 /\
  room_run RF b (snd (fst (jr_value jr_strtod d (rest_at tb text p) []))).

Definition pv_post (d : nat) L A regs mem md Lam peak cnt fail b q text len p tb v : config -> Prop :=
  fun c' => exists (fx' : YK11.FPState) L' A' regs' mem' md' Lam' peak' cnt' fail' ok res tr okr D,
     c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom segs)) md' /\
     frm_zero (@fp_csr fx') /\ fregs_kept fx fx' /\
     rpost B API (PARSE_VALUE_K d) L A regs mem md (rd_writes q v D) (fun _ _ => False) L' A' regs' mem' md' /\
     rd_cells B mem' /\
     ledger B L' A' mem' Lam' peak' cnt' fail' /\
     jr_value jr_strtod d (rest_at tb text p) ok = (res, tr, okr) /\
     oks ok cnt fail (calls tr) /\
     cnt' = cnt + Z.of_nat (calls tr) /\
     fail_after cnt fail (calls tr) fail' /\
     Permutation Lam' (D ++ Lam) /\ Permutation (map snd D) (map Z.of_nat (lsz tr)) /\ Z.of_nat (length D) = nlive tr /\ new_blks L A D /\
     peak' = Z.max peak (lsum Lam + hpeak tr) /\
     hpeak tr <= 224 * Z.of_nat (length (rest_at tb text p)) + 512 * Z.of_nat (MAXD - d) /\
     rf_ok RF A' (rf_run RF b tr) /\
     match res with
     | Some (t, r) =>
         getr regs' 10 = Z_to_bv 64 0 /\
         pj_in_ok segs mem' q text len (text + len - Z.of_nat (length r)) (Z.of_nat d) tb /\
         pj_node segs mem' (lin Lam') v t D /\
         lsum D <= 224 * (Z.of_nat (length (rest_at tb text p)) - Z.of_nat (length r))
     | None =>
         getr regs' 10 = Z_to_bv 64 (-1) /\
         pj_in_after B mem' q text len (Z.of_nat d) 33 /\
         pj_fd segs mem' (lin Lam') (MAXD - d) v D
     end.

Lemma pv_fd_zero : forall mem Lam d v, pj_zero segs mem v -> pj_fd segs mem (lin Lam) (MAXD - d) v [].
Proof.
  intros mem Lam d v H. pose proof (pj_node_fd segs JNull mem (lin Lam) v [] (pj_zero_node segs mem (lin Lam) v H)) as F.
  apply (pj_fd_mono segs mem (lin Lam) (depth JNull)); [cbn [depth]; lia | exact F].
Qed.

Lemma pv_after_ok : forall mem q text len P d tb, pj_in_ok segs mem q text len P (Z.of_nat d) tb ->
  pj_in_after B mem q text len (Z.of_nat d) 33.
Proof.
  intros mem q text len P d tb H. pose proof (pj_in_ok_bounds segs _ _ _ _ _ _ _ H) as (_ & _ & _ & B4 & _ & _ & _ & _ & B9).
  destruct H as (H1 & H2 & H3 & H4 & _). exists P, (Z.of_nat d).
  split; [lia|]. split; [lia|]. split; [exact H1|]. split; [exact H2|]. split; [exact H3 | exact H4].
Qed.

Lemma ret_pc_of : forall regs, YK0s.ret_ok (getr regs 1) -> MState.ret_pc (getr regs 1) = getr regs 1.
Proof. intros regs H. apply kb_ret_pc. exact H. Qed.

Lemma pv_model_refuse : forall d x, skip x = [] \/ (exists b0 y, skip x = b0 :: y /\ other_b b0 /\ num_tok (b0 :: y) = None) ->
  jr_value jr_strtod d x [] = (None, [], []).
Proof.
  intros d x H. rewrite jr_value_unfold. destruct H as [H|(b0 & y & H & Ho & Hn)]; rewrite H; [reflexivity|].
  destruct Ho as (O1 & O2 & O3 & O4 & O5 & O6).
  rewrite (proj2 (Z.eqb_neq b0 123) O1), (proj2 (Z.eqb_neq b0 91) O2), (proj2 (Z.eqb_neq b0 34) O3),
    (proj2 (Z.eqb_neq b0 116) O4), (proj2 (Z.eqb_neq b0 102) O5), (proj2 (Z.eqb_neq b0 110) O6).
  rewrite jr_number_tok, Hn. reflexivity.
Qed.

Lemma pv_mid_A0 : forall d L A regs mem md q m' (E : Z -> Prop) W,
  ms_segs B = rsegs -> call_pre_k B MR (PARSE_VALUE_K d) L A regs mem md -> (d <= MAXD)%nat ->
  spZ regs <= q -> Frame.munch W mem m' -> Frame.wmono segs mem m' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x -> spZ regs - 64 <= x < spZ regs \/ (q <= x /\ E x)) ->
  pv_mid B API (PARSE_VALUE_K d) (spZ regs) L A mem md E L A m' md.
Proof.
  intros d L A regs mem md q m' E W SEG PRE Hd Hq Hm Hw HW.
  pose proof PRE as (HM & HWF & HB & _ & _ & Hlo & _ & HWs & _ & Her & _).
  pose proof (pvk_bounds d Hd) as (K1 & _). pose proof ceil_big as Cb.
  apply (mid_A B API (pv_img_low SEG) _ _ L A mem md m' W E); try assumption.
  - intros a [Ha|Ha]; [apply HWs; exact Ha | apply Her; exact Ha].
  - intros x Hx Ho. destruct (HW x Hx Ho) as [H|[_ H]]; [left; left; lia | right; exact H].
  - intros x Hx Ho Hown. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM Hown). destruct (HW x Hx Ho); lia.
  - intros p n i Hin Hi Ho. exfalso. destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ p n i HM Hin Hi) as (_ & H1 & H2 & _).
    destruct (HW (ptr_addr L p + i) ltac:(lia) Ho); lia.
Qed.

Lemma pv_ledger_A0 : forall d L A regs mem md Lam peak cnt fail q m' W,
  call_pre_k B MR (PARSE_VALUE_K d) L A regs mem md -> (d <= MAXD)%nat ->
  ledger B L A mem Lam peak cnt fail -> spZ regs <= q -> Frame.munch W mem m' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x -> spZ regs - 64 <= x) ->
  ledger B L A m' Lam peak cnt fail.
Proof.
  intros d L A regs mem md Lam peak cnt fail q m' W PRE Hd HL Hq Hm HW.
  pose proof PRE as (HM & _ & _ & _ & _ & Hlo & _).
  pose proof (pvk_bounds d Hd) as (K1 & _). pose proof ceil_big as Cb.
  apply (ledger_A B API L A mem md m' W Lam peak cnt fail HM HL Hm).
  intros x Hx Ho. specialize (HW x Hx Ho). split.
  - unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL. lia.
  - intros a k Hin. pose proof (ledger_block_range B API L A mem md Lam peak cnt fail a k HM HL Hin).
    destruct HL as (_ & _ & _ & _ & _ & FB). rewrite Forall_forall in FB. destruct (FB _ Hin) as (Hk & _). cbn in Hk. lia.
Qed.

Lemma pv_cells_A0 : forall d regs mem m' W,
  ms_segs B = rsegs -> ms_got_guard B = strtod_c.STRTOD_GOT_GUARD -> ms_guard B = strtod_c.STRTOD_GUARD ->
  strtod_c.STRTOD_GLOBALS_TOP <= spZ regs - PARSE_VALUE_K d -> (d <= MAXD)%nat ->
  rd_cells B mem -> Frame.munch W mem m' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x -> spZ regs - 64 <= x) ->
  rd_cells B m'.
Proof.
  intros d regs mem m' W SEG GG GD GT Hd RC Hm HW.
  pose proof (pvk_bounds d Hd) as (K1 & _).
  unfold strtod_c.STRTOD_GLOBALS_TOP, strtod_c.STRTOD_GOT_GUARD, strtod_c.STRTOD_GUARD in *.
  apply (rd_cells_A B mem m' W RC Hm); rewrite ?GG, ?GD; try lia.
  - intros x Hro. pose proof (ro_low SEG x Hro). pose proof (bv_unsigned_in_range 64 x) as R.
    unfold bv_modulus in R. destruct (kb_outside_dec W (bv_unsigned x)) as [Ho|Ho]; [exact Ho|].
    exfalso. cbn in R. specialize (HW (bv_unsigned x) ltac:(lia) Ho). lia.
  - intros k Hk. unfold strtod_c.STRTOD_GOT_GUARD, strtod_c.STRTOD_GUARD.
    split; match goal with |- Frame.outside W ?a =>
      destruct (kb_outside_dec W a) as [Ho|Ho]; [exact Ho|]; exfalso; specialize (HW a ltac:(lia) Ho); lia end.
Qed.

Lemma pv_path_ret : forall d L A regs mem md Lam peak cnt fail b q text len p tb v,
  pv_pre d L A regs mem md Lam peak cnt fail b q text len p tb v ->
  forall P m' regs',
  text <= P <= text + len -> rest_at tb text P = skip (rest_at tb text p) ->
  pj_in_ok rsegs m' q text len P (Z.of_nat d) tb -> Frame.wmono rsegs mem m' ->
  (rest_at tb text P = [] \/ exists b0 y, rest_at tb text P = b0 :: y /\ other_b b0 /\ num_tok (b0 :: y) = None) ->
  Frame.munch [(spZ regs - 64, spZ regs); (q, q + 8)] mem m' ->
  pj_zero rsegs m' v ->
  regs_preserved regs regs' -> getr regs' 10 = Z_to_bv 64 (-1) ->
  SR segs (mkCfg (mkst regs' (MState.ret_pc (getr regs 1)) m' (seg_rom segs)) md)
    (pv_post d L A regs mem md Lam peak cnt fail b q text len p tb v).
Proof.
  intros d L A regs mem md Lam peak cnt fail b q text len p tb v PRE P m' regs' HP HR PJ WM Hc MU PZ RP R10.
  destruct PRE as (ENV & LED & RES & Q10 & V11 & PJ0 & Hq & QA & MX & TX & V0 & VZ & VP & D1 & D2 & CN & RR).
  destruct ENV as (SEG & TP & EA & GG & GD & PRE & H47 & GT & FRM & RC).
  pose proof (pj_in_ok_bounds segs _ _ _ _ _ _ _ PJ0) as (_ & _ & _ & _ & _ & _ & _ & _ & Bd).
  assert (Hd : (d <= MAXD)%nat) by (unfold MAXD; lia).
  pose proof PRE as (HM & HWF & HB & HRA & _ & Hlo & _).
  pose proof (pvk_bounds d Hd) as (K1 & _).
  assert (HW : forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside [(spZ regs - 64, spZ regs); (q, q + 8)] x ->
                 spZ regs - 64 <= x < spZ regs \/ (q <= x /\ rd_writes q v [] x)).
  { intros x Hx Ho. destruct (outside2 _ _ _ _ _ Ho) as [H|H]; [left; exact H|].
    right. split; [lia|]. right. left. left. exact H. }
  assert (HW' : forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside [(spZ regs - 64, spZ regs); (q, q + 8)] x -> spZ regs - 64 <= x)
    by (intros x Hx Ho; destruct (HW x Hx Ho) as [H|[H _]]; lia).
  rewrite <- SEG in WM, PJ, PZ.
  pose proof (pv_mid_A0 d L A regs mem md q m' (rd_writes q v []) _ SEG PRE Hd Hq MU WM HW) as MID.
  apply SR_ret. unfold pv_post.
  exists fx, L, A, regs', m', md, Lam, peak, cnt, fail, [], (@None (jv * list Z)), [], [], [].
  split; [rewrite (ret_pc_of regs HRA); reflexivity|].
  split; [exact FRM|]. split; [intros r Hr; reflexivity|].
  split; [exact (mid_rpost B API _ L A regs mem md _ L A regs' m' md MID RP)|].
  split; [exact (pv_cells_A0 d regs mem m' _ SEG GG GD GT Hd RC MU HW')|].
  split; [exact (pv_ledger_A0 d L A regs mem md Lam peak cnt fail q m' _ PRE Hd LED Hq MU HW')|].
  split; [apply pv_model_refuse; rewrite <- HR; exact Hc|].
  split; [apply oks_zero|]. split; [cbn; lia|]. split; [apply fail_after_zero|].
  split; [apply Permutation_refl|]. split; [apply Permutation_refl|]. split; [reflexivity|]. split; [intros a k []|].
  split; [destruct LED as (_ & (LP & _) & _); cbn [hpeak]; lia|].
  split; [cbn [hpeak]; lia|].
  split; [exact RES|].
  split; [exact R10|]. split; [exact (pv_after_ok m' q text len P d tb PJ)|]. exact (pv_fd_zero m' Lam d v PZ).
Qed.

End M.
