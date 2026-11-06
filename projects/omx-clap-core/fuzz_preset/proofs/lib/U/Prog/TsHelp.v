From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract MemNorm KindBGlue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require RegisterBridge Regs6ss.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct WriterSpec WriterSpecFacts.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import
tx_put_c TxRet TxGlue TxCompose TxTree Ledger GIInit TsRuns TsGo.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import TxCalls.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition accs (bs : list Z) (i : Z) : list byte := map (Z_to_bv 8) (34 :: escaped (firstn (Z.to_nat i) bs)).

Definition cat (bs : list Z) (i : Z) : Z := nth (Z.to_nat i) (bs ++ [0]) 0.

Definition piece (c : Z) : list Z := if special c then esc c else [c].

Lemma firstn_snoc : forall (l : list Z) n, (n < length l)%nat -> firstn (S n) l = firstn n l ++ [nth n l 0].
Proof.
  induction l as [|x l IH]; intros n Hn; cbn [length] in Hn; [lia|].
  destruct n as [|n]; [reflexivity|]. cbn [firstn nth app]. f_equal. apply IH. lia.
Qed.

Lemma accs_step : forall bs i, 0 <= i < Z.of_nat (length bs) ->
  accs bs (i + 1) = accs bs i ++ map (Z_to_bv 8) (piece (cat bs i)).
Proof.
  intros bs i Hi. unfold accs, cat, piece.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  rewrite firstn_snoc by lia. unfold escaped. rewrite flat_map_app. cbn [flat_map]. rewrite app_nil_r.
  rewrite app_nth1 by lia. cbn [map]. rewrite map_app. reflexivity.
Qed.

Lemma accs_full : forall bs, accs bs (Z.of_nat (length bs)) ++ [Z_to_bv 8 34] = map (Z_to_bv 8) (wstr bs).
Proof.
  intros bs. unfold accs. rewrite Nat2Z.id, firstn_all, wstr_spec. cbn [map app]. rewrite map_app. reflexivity.
Qed.

Lemma escaped_le : forall bs n, (length (escaped (firstn n bs)) <= length (escaped bs))%nat.
Proof.
  intros bs n. rewrite <- (firstn_skipn n bs) at 2. unfold escaped. rewrite flat_map_app, length_app. lia.
Qed.

Lemma accs_len : forall bs i, Z.of_nat (length (accs bs i)) = 1 + Z.of_nat (length (escaped (firstn (Z.to_nat i) bs))).
Proof. intros bs i. unfold accs. rewrite length_map. cbn [length]. lia. Qed.

Lemma wstr_len : forall bs, Z.of_nat (length (map (Z_to_bv 8) (wstr bs))) = 2 + Z.of_nat (length (escaped bs)).
Proof. intros bs. rewrite length_map, wstr_spec. cbn [length]. rewrite length_app. cbn [length]. lia. Qed.

Lemma cat_lt : forall bs i, 0 <= i < Z.of_nat (length bs) -> cat bs i = nth (Z.to_nat i) bs 0.
Proof. intros bs i Hi. unfold cat. apply app_nth1. lia. Qed.

Lemma cat_facts : forall bs i, Forall (fun c => 0 < c < 256) bs -> 0 <= i <= Z.of_nat (length bs) ->
  0 <= cat bs i < 256 /\ (cat bs i = 0 <-> i = Z.of_nat (length bs)).
Proof.
  intros bs i HF Hi. destruct (Z.eq_dec i (Z.of_nat (length bs))) as [E|E].
  - unfold cat. rewrite E, Nat2Z.id, app_nth2 by lia. rewrite Nat.sub_diag. cbn. split; [lia | tauto].
  - rewrite cat_lt by lia. rewrite Forall_forall in HF.
    assert (H : 0 < nth (Z.to_nat i) bs 0 < 256) by (apply HF; apply nth_In; lia). split; [lia|]. split; lia.
Qed.

Lemma firstn1_map : forall (l : list Z) n, (n < length l)%nat ->
  firstn 1 (skipn n (map (Z_to_bv 8) l)) = [Z_to_bv 8 (nth n l 0)].
Proof.
  induction l as [|x l IH]; intros n Hn; cbn [length] in Hn; [lia|].
  destruct n as [|n]; [reflexivity|]. cbn [map skipn nth]. apply IH. lia.
Qed.

Lemma special_q : forall c, c = 34 \/ c = 92 -> piece c = [92; c].
Proof. intros c [->| ->]; reflexivity. Qed.

Lemma special_p : forall c, 32 <= c -> c <> 34 -> c <> 92 -> piece c = [c].
Proof.
  intros c H1 H2 H3. unfold piece, special.
  rewrite (proj2 (Z.eqb_neq c 34)) by lia. rewrite (proj2 (Z.eqb_neq c 92)) by lia.
  rewrite (proj2 (Z.ltb_ge c 32)) by lia. reflexivity.
Qed.

Lemma special_c : forall c, c < 32 -> piece c = esc c.
Proof.
  intros c H. unfold piece, special. rewrite (proj2 (Z.ltb_lt c 32)) by lia.
  rewrite !orb_true_r. reflexivity.
Qed.

Lemma piece_len : forall c, 0 <= c < 256 -> 1 <= Z.of_nat (length (piece c)) <= 6.
Proof.
  intros c Hc. unfold piece, esc.
  destruct (special c); [|cbn; lia].
  destruct (c =? 34); [cbn; lia|]. destruct (c =? 92); [cbn; lia|]. destruct (c =? 10); [cbn; lia|].
  destruct (c =? 9); [cbn; lia|]. destruct (c =? 13); cbn; lia.
Qed.

Lemma escaped_snoc_len : forall bs i, 0 <= i < Z.of_nat (length bs) ->
  Z.of_nat (length (escaped (firstn (Z.to_nat i) bs))) + Z.of_nat (length (piece (cat bs i))) <=
  Z.of_nat (length (escaped bs)).
Proof.
  intros bs i Hi. pose proof (escaped_le bs (S (Z.to_nat i))) as H.
  rewrite firstn_snoc in H by lia. unfold escaped in H. rewrite flat_map_app, length_app in H.
  cbn [flat_map] in H. rewrite app_nil_r in H. rewrite cat_lt by lia. unfold piece, escaped. lia.
Qed.

Definition ksb (bs : list Z) (i : Z) : list Z := plen ([34] :: concat (map spcs (firstn (Z.to_nat i) bs))).

Lemma split_nth : forall (l : list Z) i, (i < length l)%nat -> l = firstn i l ++ nth i l 0 :: skipn (S i) l.
Proof.
  induction l as [|x l IH]; intros [|i] Hi; cbn [length] in Hi; try lia; [reflexivity|].
  cbn [firstn nth skipn app]. f_equal. apply IH. lia.
Qed.

Lemma ksb_step : forall bs i, 0 <= i < Z.of_nat (length bs) -> ksb bs (i + 1) = ksb bs i ++ plen (spcs (cat bs i)).
Proof.
  intros bs i Hi. unfold ksb. replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  rewrite (firstn_snoc bs (Z.to_nat i)) by lia. rewrite map_app, concat_app. cbn [map concat]. rewrite app_nil_r.
  rewrite cat_lt by exact Hi. unfold plen. cbn [map]. rewrite map_app. reflexivity.
Qed.

Lemma ksb_full : forall bs, ksb bs (Z.of_nat (length bs)) ++ [1] = plen (strp bs).
Proof. intros bs. unfold ksb, strp. rewrite Nat2Z.id, firstn_all. unfold plen. cbn [map]. rewrite map_app. reflexivity. Qed.

Lemma ksb_split : forall bs i, 0 <= i < Z.of_nat (length bs) ->
  exists rest, plen (strp bs) = ksb bs i ++ plen (spcs (cat bs i)) ++ rest.
Proof.
  intros bs i Hi. pose proof (split_nth bs (Z.to_nat i) ltac:(lia)) as E.
  exists (plen (concat (map spcs (skipn (S (Z.to_nat i)) bs)) ++ [[34]])).
  unfold strp, ksb. rewrite cat_lt by exact Hi.
  set (u := firstn (Z.to_nat i) bs) in *. set (x := nth (Z.to_nat i) bs 0) in *.
  set (w := skipn (S (Z.to_nat i)) bs) in *. clearbody u x w. rewrite E.
  rewrite map_app, concat_app. cbn [map concat]. unfold plen. cbn [map]. rewrite !map_app. rewrite <- !app_assoc.
  reflexivity.
Qed.

Lemma spcs_p : forall c, 32 <= c -> c <> 34 -> c <> 92 -> spcs c = [[c]].
Proof.
  intros c H1 H2 H3. unfold spcs, special.
  rewrite (proj2 (Z.eqb_neq c 34)) by lia. rewrite (proj2 (Z.eqb_neq c 92)) by lia.
  rewrite (proj2 (Z.ltb_ge c 32)) by lia. reflexivity.
Qed.

Lemma spcs_c : forall c, c < 32 -> spcs c = [esc c].
Proof.
  intros c H. unfold spcs, special.
  rewrite (proj2 (Z.eqb_neq c 34)) by lia. rewrite (proj2 (Z.eqb_neq c 92)) by lia.
  rewrite (proj2 (Z.ltb_lt c 32)) by lia. reflexivity.
Qed.

Lemma spcs_b : forall c, c = 34 \/ c = 92 -> spcs c = [[92]; [c]].
Proof. intros c [->| ->]; reflexivity. Qed.

Definition canR (r : bvmap 5 word) :=
  mkR (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr r 1) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr r 2) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr r 3) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr r 4) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr r 5) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr r 6)
      (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr r 7) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr r 8) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr r 9) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr r 10) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr r 11) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr r 12)
      (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr r 13) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr r 14) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr r 15) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr r 16) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr r 17) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr r 18)
      (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr r 19) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr r 20) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr r 21) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr r 22) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr r 23) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr r 24)
      (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr r 25) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr r 26) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr r 27) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr r 28) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr r 29) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr r 30)
      (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr r 31).

Ltac rp RP HR r :=
  first [ etransitivity; [exact (RP r ltac:(unfold callee_saved; lia)) | gval HR]
        | symmetry; etransitivity; [exact (RP r ltac:(unfold callee_saved; lia)) | gval HR] ].

Ltac rpa RP HR := lazymatch goal with |- OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr _ ?k = _ =>
  let kz := eval vm_compute in (bv_unsigned k) in rp RP HR kz end.

Section KB.
Context {fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState} {rc : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis ERRB : errno_addr B + 4 <= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling.
Hypothesis AX : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable.YL01.AllocExtra B (aa_MR API).
Hypothesis CTX : ctx_owned B API.
Hypothesis HG : globals_free B API omx_G.
#[local] Set Default Proof Using "All".

Lemma ts_gst : forall a, alloc_statics a -> in_img B a /\ ~ (errno_addr B <= a < errno_addr B + 4) /\
  forall L A mem md, aa_MR API L A mem md -> ~ owned B L A a.
Proof.
  intros a Ha. assert (HI : in_globals omx_G a).
  { unfold in_globals, omx_G. destruct Ha as [H|[H|[H|H]]].
    - exists G_LIVE, 8. split; [left; reflexivity | exact H].
    - exists G_PEAK, 8. split; [right; left; reflexivity | exact H].
    - exists G_COUNT, 8. split; [right; right; left; reflexivity | exact H].
    - exists G_FAIL, 8. split; [right; right; right; left; reflexivity | exact H]. }
  destruct (HG a HI) as (Hi & _ & _ & He & Ho). split; [exact Hi|]. split; [exact He|].
  intros L A mem md M. exact (proj1 (Ho L A mem md M)).
Qed.

Lemma img1 : forall m a v, ro_agree (ms_segs B) m -> ro_addr rsegs (Z_to_bv 64 (a + 0)) = true ->
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom rsegs (Z_to_bv 64 (a + 0)) = Some (Z_to_bv 8 v) -> mbytes B m a [Z_to_bv 8 v].
Proof.
  intros m a v RA RO E i Hi. cbn [length Z.of_nat] in Hi. rewrite SEGS in RA |- *.
  assert (i = 0) as -> by lia.
  transitivity (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom rsegs (Z_to_bv 64 (a + 0))); [exact (RA _ RO) | exact E].
Qed.

Lemma hex_img : forall m, ro_agree (ms_segs B) m -> bytes_at rsegs m 0x104a8 hexl.
Proof.
  intros m RA. apply (mbytes_bytes_at B SEGS); [lia | cbn [length Z.of_nat]; lia |].
  intros i Hi. simpl in Hi. rewrite SEGS in RA |- *.
  assert (E : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/
              i = 11 \/ i = 12 \/ i = 13 \/ i = 14 \/ i = 15) by lia.
  repeat destruct E as [E|E]; subst i;
    match goal with |- mbyte _ _ (0x104a8 + ?x) = _ =>
      let RO := fresh "RO" in
      assert (RO : ro_addr rsegs (Z_to_bv 64 (0x104a8 + x)) = true) by (vm_compute; reflexivity);
      transitivity (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom rsegs (Z_to_bv 64 (0x104a8 + x))); [exact (RA _ RO) | vm_compute; reflexivity]
    end.
Qed.

Lemma mbytes_one : forall m a (l : list Z) i, mbytes B m a (map (Z_to_bv 8) l) -> 0 <= i < Z.of_nat (length l) ->
  mbytes B m (a + i) [Z_to_bv 8 (nth (Z.to_nat i) l 0)].
Proof.
  intros m a l i H Hi j Hj. cbn [length Z.of_nat] in Hj. assert (j = 0) as -> by lia. rewrite Z.add_0_r.
  rewrite (H i) by (rewrite length_map; lia). rewrite nth_error_map. rewrite (nth_error_nth' l 0) by lia.
  reflexivity.
Qed.

Variable F : ResForm.

Lemma tx_relx_store : forall stk L A regs mem md t b0 len0 cap0 txt bnd ns need acc L1 A1 mem1 md1 b1 cap1 j1 mem2 lo hi,
  tx_start B API F stk L A regs mem md t b0 len0 cap0 txt bnd ns need ->
  tx_relx B API F stk regs t b0 len0 cap0 txt acc bnd L A mem md L1 A1 mem1 md1 b1 cap1 j1 ->
  munch [(lo, hi)] mem1 mem2 -> wmono rsegs mem1 mem2 -> ro_agree (ms_segs B) mem2 ->
  (forall a, lo <= a < hi -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling <= a /\ spZ regs - stk <= a < spZ regs) ->
  tx_relx B API F stk regs t b0 len0 cap0 txt acc bnd L A mem md L1 A1 mem2 md1 b1 cap1 j1.
Proof.
  intros stk L A regs mem md t b0 len0 cap0 txt bnd ns need acc L1 A1 mem1 md1 b1 cap1 j1 mem2 lo hi ST R1 MU WM RA LOHI.
  destruct (tx_start_facts B API SEGS ERRB AX CTX F _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST) as (M0 & _ & _ & _ & SPT & _ & INV0).
  pose proof ST as (_ & _ & _ & _ & _ & Thi & _).
  pose proof R1 as ((M1 & W1 & BD1 & _ & _ & _ & _ & _ & SC1) & _ & _ & _ & _ & TR1 & TW1 & INV1 & _ & _ & IN1 & _ & _ & RES1).
  pose proof (tx_rel_frame B API SEGS ERRB AX CTX F stk regs t b1 (len0 + Z.of_nat (length acc)) cap1 (txt ++ acc)
                (tx_fold F bnd len0 cap0 j1) L1 A1 mem1 md1 mem2 lo hi M1 W1 BD1 IN1 MU WM RA LOHI SPT Thi TR1 TW1 INV1 RES1 SC1) as R2.
  pose proof (tx_relx_comp B API SEGS ERRB AX CTX F stk regs t b0 len0 cap0 txt acc [] bnd L A mem md
                L1 A1 mem1 md1 b1 cap1 j1 L1 A1 mem2 md1 b1 cap1 [] M0 INV0 R1 R2) as R3.
  rewrite !app_nil_r in R3. exact R3.
Qed.

End KB.
