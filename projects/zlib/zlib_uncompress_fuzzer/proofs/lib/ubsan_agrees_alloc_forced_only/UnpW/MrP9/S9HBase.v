(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.  (* a worker (A1) tool *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require RunHit.  (* a worker (A1) miss kit *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require PropExec CatSim ShapeAlg StoreOk Frame.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainS9 Require Import PImg RMalloc_iface.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Mr Require Import MrBridge MrRegsEqvW MrEqv. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Mr Require Import MrRulesS9.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module OP := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.PropExec.
Module OF := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Frame.
Module OS := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.StoreOk.

Abbreviation realizes := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.ShapeAlg.realizes.
Abbreviation fc0 := (Z_to_bv 32 0).

(* [comment removed for export] *)

Lemma rz_evt {RCa1 : RunCtx}  : forall ms mo T,
  m_halted mo = None -> m_vm_lazy mo = [] ->
  evt (run_segments psegs rc_inp rc_sp rc_mb) (fun ms' => realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg ms' mo) T) ms ->
  realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg ms mo) T.
Proof.
  intros ms mo T Hh Hl (ms' & Hms & HQ).
  eapply ShapeAlg.rz_msteps; [exact Hh | exact Hl | apply B.msteps_ut_ours; exact Hms | exact HQ].
Qed.

Lemma rz_mkR {RCa1 : RunCtx}  : forall R pc M mo T,
  realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (MS (mkR_of R) bvmap_empty pc fc0 None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo) T ->
  realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (OP.mkst (fx := OP.fx0) R pc M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo) T.
Proof.
  intros R pc M mo T H. eapply realizes_eqv; [exact H|].
  split; [|reflexivity]. cbn. split; [apply mkR_of_eqvW|]. repeat split; apply regs_eqv_refl.
Qed.

(* [comment removed for export] *)
Lemma rz_ours {RCa1 : RunCtx}  : forall ms ms' mo T,
  m_halted mo = None -> m_vm_lazy mo = [] ->
  CatSim.msteps (run_segments psegs rc_inp rc_sp rc_mb) ms ms' -> realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg ms' mo) T -> realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg ms mo) T.
Proof. intros. eapply ShapeAlg.rz_msteps; eassumption. Qed.

(* [comment removed for export] *)

Definition same_on {RCa1 : RunCtx}  (P : Z -> Prop) (m m' : word -> option byte) : Prop :=
  forall a, 0 <= a < 2^64 -> P a ->
    m' (wa a) = m (wa a) /\ (wview (run_segments psegs rc_inp rc_sp rc_mb) m (wa a) <> None -> wview (run_segments psegs rc_inp rc_sp rc_mb) m' (wa a) <> None).

Lemma same_on_refl {RCa1 : RunCtx}  : forall P m, same_on P m m.
Proof. intros P m a _ _. auto. Qed.

Lemma same_on_trans {RCa1 : RunCtx}  : forall P m1 m2 m3, same_on P m1 m2 -> same_on P m2 m3 -> same_on P m1 m3.
Proof.
  intros P m1 m2 m3 H1 H2 a Ha Hp. destruct (H1 a Ha Hp) as [E1 W1]. destruct (H2 a Ha Hp) as [E2 W2].
  split; [congruence | auto].
Qed.

Lemma same_on_weaken {RCa1 : RunCtx}  : forall (P P' : Z -> Prop) m m', same_on P m m' -> (forall a, P' a -> P a) -> same_on P' m m'.
Proof. intros P P' m m' H HP a Ha Hp. apply H; auto. Qed.

Lemma same_on_munch {RCa1 : RunCtx}  : forall W m m', munch W m m' -> wmono (run_segments psegs rc_inp rc_sp rc_mb) m m' -> same_on (outside W) m m'.
Proof.
  intros W m m' MU WM a Ha Ho. split; [apply MU; rewrite wa_unsigned by lia; exact Ho | apply WM].
Qed.

(* [comment removed for export] *)
Lemma same_on_rheap_pres {RCa1 : RunCtx}  : forall LB SP m m', rheap_pres LB SP m m' -> same_on (rclient_addr LB SP) m m'.
Proof. intros LB SP m m' H. exact H. Qed.

(* [comment removed for export] *)
Definition pristine_in (ivs : list (Z * Z)) (M : word -> option byte) : Prop :=
  forall lo hi a, In (lo, hi) ivs -> lo <= a < hi -> M (Z_to_bv 64 a) = None.

Lemma pristine_in_same_on {RCa1 : RunCtx}  : forall (P : Z -> Prop) ivs M M',
  pristine_in ivs M -> same_on P M M' ->
  (forall lo hi a, In (lo, hi) ivs -> lo <= a < hi -> 0 <= a < 2^64 /\ P a) ->
  pristine_in ivs M'.
Proof.
  intros P ivs M M' PR SO HP lo hi a IN Ha. destruct (HP lo hi a IN Ha) as [R Pa].
  destruct (SO a R Pa) as [E _]. unfold wa in E. rewrite E. eapply PR; eauto.
Qed.

Lemma rdn_same_on {RCa1 : RunCtx}  : forall (P : Z -> Prop) M M' a n,
  same_on P M M' -> (forall x, a <= x < a + Z.of_nat n -> P x) -> 0 <= a < 2^64 -> a + Z.of_nat n <= 2^64 ->
  OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) M' (Z_to_bv 64 a) n = OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) M (Z_to_bv 64 a) n.
Proof.
  intros P M M' a n SO HP Ha Hn. apply OP.rdn_ext.
  - rewrite wa_unsigned by lia. lia.
  - intros x Hx. rewrite wa_unsigned in Hx by lia.
    destruct (SO (bv_unsigned x) ltac:(lia) ltac:(apply HP; lia)) as [E _].
    unfold wa in E. rewrite Z_to_bv_bv_unsigned in E. exact E.
Qed.

(* [comment removed for export] *)
Definition fm_ivs (rs : list (word * Z)) : list (Z * Z) :=
  map (fun r => (bv_unsigned (fst r), bv_unsigned (fst r) + snd r)) rs.

Lemma outside_fm_ivs : forall rs (x : word), outside (fm_ivs rs) (bv_unsigned x) -> OF.outside x rs.
Proof.
  induction rs as [|[b n] rs IH]; intros x H; cbn in *; [exact I|].
  destruct H as [H1 H2]. split; [unfold OF.in_rng; exact H1 | apply IH; exact H2].
Qed.

Lemma wmono_of_mem_grows {RCa1 : RunCtx}  : forall m m', OS.mem_grows m m' -> wmono (run_segments psegs rc_inp rc_sp rc_mb) m m'.
Proof.
  intros m m' G x H. unfold wview in *. destruct (m x) as [b|] eqn:E.
  - pose proof (G x ltac:(congruence)) as G'. destruct (m' x); [discriminate | contradiction].
  - destruct (m' x); [discriminate | exact H].
Qed.

Lemma munch_of_frame_mod {RCa1 : RunCtx}  : forall m m' rs, OF.frame_mod m m' rs -> munch (fm_ivs rs) m m' /\ wmono (run_segments psegs rc_inp rc_sp rc_mb) m m'.
Proof.
  intros m m' rs [H G]. split; [| apply wmono_of_mem_grows; exact G].
  intros x Hx. apply H. apply outside_fm_ivs. exact Hx.
Qed.

(* [comment removed for export] *)
(* a worker (A1) route (A): [iv]'s bytes OFF the image were writable before the write.  Over the run the vDSO
   pair is a read-only range off the image, so a byte that was writable is off the pair. *)
Definition wv_out {RCa1 : RunCtx} (m : word -> option byte) (iv : Z * Z) : Prop :=
  forall a, fst iv <= a < snd iv -> (a < 0x10000 \/ 0x94000 <= a) ->
    wview (run_segments psegs rc_inp rc_sp rc_mb) m (wa a) <> None.

Lemma outside_or_in : forall W x, outside W x \/ exists iv, In iv W /\ fst iv <= x < snd iv.
Proof.
  induction W as [|[l h] W IH]; intros x; cbn; [left; exact I|].
  destruct (IH x) as [O|(iv & IN & R)]; [|right; exists iv; split; [right; exact IN | exact R]].
  destruct (Z_le_gt_dec l x); destruct (Z_lt_ge_dec x h).
  - right. exists (l, h). split; [left; reflexivity | cbn; lia].
  - left. split; [lia | exact O].
  - left. split; [lia | exact O].
  - left. split; [lia | exact O].
Qed.

(* a worker (A1) route (A): on the image the run's first match is the image's. *)
Lemma run_ro_addr_img {RCa1 : RunCtx} : forall a : word, 0x10000 <= bv_unsigned a < 0x94000 ->
  ro_addr (run_segments psegs rc_inp rc_sp rc_mb) a = ro_addr psegs a.
Proof.
  intros a Ha. unfold ro_addr.
  destruct (find_segment psegs (bv_unsigned a) 1) as [s|] eqn:E.
  - unfold run_segments. rewrite (RunHit.find_segment_app_hit _ _ _ _ _ E). reflexivity.
  - exfalso. rewrite p_find_segment_1 in E by lia.
    destruct (Z.leb_spec0 0x10000 (bv_unsigned a)); destruct (Z.leb_spec0 (bv_unsigned a + 1) 0x14000);
    destruct (Z.leb_spec0 0x14000 (bv_unsigned a)); destruct (Z.leb_spec0 (bv_unsigned a + 1) 0x21000);
    destruct (Z.leb_spec0 0x21000 (bv_unsigned a)); destruct (Z.leb_spec0 (bv_unsigned a + 1) 0x22000);
    destruct (Z.leb_spec0 0x22000 (bv_unsigned a)); destruct (Z.leb_spec0 (bv_unsigned a + 1) 0x94000);
    cbn in E; try discriminate E; lia.
Qed.

Lemma mem_inv_munch {RCa1 : RunCtx}  : forall W m m', mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m -> munch W m m' ->
  (forall a, 0x10000 <= a < 0x21000 -> outside W a) ->
  Forall (wv_out m) W ->  (* a worker (A1) route (A): the bytes written off the image were writable *)
  mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m'.
Proof.
  intros W m m' MI MU HW HV a b Hab. pose proof (bv_unsigned_in_range 64 a) as Ra.
  destruct (Z_lt_le_dec (bv_unsigned a) 0x94000) as [L2|L2];
    [destruct (Z_lt_le_dec (bv_unsigned a) 0x10000) as [L1|L1]|].
  2: { rewrite run_ro_addr_img by lia. rewrite p_ro_addr.
       destruct ((65536 <=? bv_unsigned a) && (bv_unsigned a <? 135168))%bool eqn:E; [|reflexivity].
       apply andb_prop in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
       rewrite (MU a (HW (bv_unsigned a) ltac:(lia))) in Hab. pose proof (MI a b Hab) as X.
       rewrite run_ro_addr_img, p_ro_addr in X by lia.
       rewrite <- X. symmetry. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  all: destruct (outside_or_in W (bv_unsigned a)) as [O|(iv & IN & R)];
         [rewrite (MU a O) in Hab; exact (MI a b Hab)|].
  all: pose proof (proj1 (Forall_forall _ _) HV iv IN (bv_unsigned a) R ltac:(lia)) as WV;
       unfold wa in WV; rewrite Z_to_bv_bv_unsigned in WV;
       destruct (m a) as [b0|] eqn:E; [exact (MI a b0 E) | exact (wview_not_ro _ _ _ WV E)].
Qed.

(* [comment removed for export] *)
Lemma rz_kept {RCa1 : RunCtx}  : forall (R R' : bvmap 5 word) pc M mo T,
  (forall k, In k kept_regs -> reg_get R' (Z_to_bv 5 k) = reg_get R (Z_to_bv 5 k)) ->
  (let g := fun k : Z => reg_get R (Z_to_bv 5 k) in let g' := fun k : Z => reg_get R' (Z_to_bv 5 k) in
   realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (MS (mkR (g 1) (g 2) (g 3) (g 4) (g' 5) (g' 6) (g' 7) (g 8) (g 9) (g' 10) (g' 11) (g' 12) (g' 13) (g' 14) (g' 15)
                                   (g' 16) (g' 17) (g 18) (g 19) (g 20) (g 21) (g 22) (g 23) (g 24) (g 25) (g 26) (g 27)
                                   (g' 28) (g' 29) (g' 30) (g' 31))
                              bvmap_empty pc fc0 None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo) T) ->
  realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (OP.mkst (fx := OP.fx0) R' pc M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo) T.
Proof.
  intros R R' pc M mo T KEPT H. apply rz_mkR. unfold mkR_of. cbv zeta in H.
  rewrite (KEPT 1 ltac:(cbn; tauto)), (KEPT 2 ltac:(cbn; tauto)), (KEPT 3 ltac:(cbn; tauto)), (KEPT 4 ltac:(cbn; tauto)),
          (KEPT 8 ltac:(cbn; tauto)), (KEPT 9 ltac:(cbn; tauto)), (KEPT 18 ltac:(cbn; tauto)), (KEPT 19 ltac:(cbn; tauto)),
          (KEPT 20 ltac:(cbn; tauto)), (KEPT 21 ltac:(cbn; tauto)), (KEPT 22 ltac:(cbn; tauto)), (KEPT 23 ltac:(cbn; tauto)),
          (KEPT 24 ltac:(cbn; tauto)), (KEPT 25 ltac:(cbn; tauto)), (KEPT 26 ltac:(cbn; tauto)), (KEPT 27 ltac:(cbn; tauto)).
  exact H.
Qed.
