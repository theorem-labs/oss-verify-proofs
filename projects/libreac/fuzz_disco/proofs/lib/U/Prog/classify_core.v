From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge Image.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import RcModel RcLib RcLeaf RcParse CtrlParsed disco_classify_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import bcmp_c memset_c reac_ctrl_parse_c reac_ctrl_checksum_verify_c reac_ports_parse_c classify_core_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require disco_table.
Import ListNotations.
Open Scope Z_scope.

Definition cc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (lo o r : Z) (OUT : list byte) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp - 192, bv_unsigned sp); (o, o + 24)] m m' /\
    wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
    rw_cells rsegs m' o [CB 24 OUT].

Lemma cc_exit : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (sp0 vra v0 v1 v2 v3 v4 v5 v6 : word) (lo o r : Z)
    (OUT : list byte) (cw cq : list cell),
  sp = Z_to_bv 64 (bv_unsigned sp0 + -112) -> lo + 192 <= bv_unsigned sp0 ->
  stk rsegs m lo (bv_unsigned sp0 + -112) ->
  rw_cells rsegs m (bv_unsigned sp0 + -112) cw -> cells_size cw = 12%nat ->
  rw_cells rsegs m (bv_unsigned sp0 + -100) cq -> cells_size cq = 36%nat ->
  rw_cells rsegs m (bv_unsigned sp0 + -64) [C8 v6; C8 v5; C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 vra] ->
  rw_cells rsegs m o [CB 24 OUT] -> mem_inv rsegs m ->
  evt rsegs (cc_post vra sp0 gp tp v0 v1 v2 v3 v4 v5 v6 s7 s8 s9 s10 s11 F fc m lo o r OUT)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 r) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1567c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m sp0
    vra v0 v1 v2 v3 v4 v5 v6 lo o r OUT cw cq Esp LO ST HW Hw HQ Hq SV HO HI.
  subst sp.
  pose proof (bv_unsigned_in_range 64 sp0) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof ST as (Slo & Shi & _).
  do 11 step.
  apply evt_done. unfold cc_post.
  exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m.
  split; [reflexivity|].
  split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact HI|]. split; [|exact HO].
  pose proof (stk_release rsegs m lo _ cw ST HW ltac:(lia)) as S1. rewrite Hw in S1.
  replace (bv_unsigned sp0 + -112 + Z.of_nat 12) with (bv_unsigned sp0 + -100) in S1 by lia.
  pose proof (stk_release rsegs m lo _ cq S1 HQ ltac:(lia)) as S2. rewrite Hq in S2.
  replace (bv_unsigned sp0 + -100 + Z.of_nat 36) with (bv_unsigned sp0 + -64) in S2 by lia.
  pose proof (stk_release rsegs m lo _ _ S2 SV ltac:(lia)) as S3. cbn [cells_size csize Nat.add] in S3.
  replace (bv_unsigned sp0 + -64 + Z.of_nat 64) with (bv_unsigned sp0) in S3 by lia. exact S3.
Qed.

Definition sbh (F : list byte) (r : Z) : list byte := src F ++ [zb 0; zb 0] ++ le4 (Z_to_bv 64 r).
Definition sbo (F : list byte) (r : Z) (d : list byte) (sl g : Z) : list byte :=
  sbh F r ++ d ++ [zb 0; zb sl; zb 0; zb 0; zb 0] ++ le4 (Z_to_bv 64 g).
Definition dbytes (F : list byte) : list byte :=
  match sdecl F with Some (i, o) => [zb 1; zb i; zb o] | None => [zb 0; zb 0; zb 0] end.

Lemma kq_div : forall x, 0 <= x < 2^64 ->
  bv_unsigned (Z_to_bv 64 ((x * 16397105843297379215) ≫ 64)) ≫ 5 = x / 36.
Proof.
  intros x Hx.
  assert (B : 0 <= x * 16397105843297379215 / 2 ^ 64 < 2 ^ 64).
  { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia. }
  rewrite (Z.shiftr_div_pow2 _ 64) by lia. rewrite unsigned_lit by exact B.
  rewrite Z.shiftr_div_pow2, Z.div_div by lia.
  symmetry. apply Z.div_unique with (r := x * 16397105843297379215 - 2 ^ 64 * 2 ^ 5 * (x / 36)).
  - left. pose proof (Z.div_mod x 36 ltac:(lia)). pose proof (Z.mod_pos_bound x 36 ltac:(lia)).
    pose proof (Z.div_pos x 36 ltac:(lia) ltac:(lia)). assert (x / 36 < 2 ^ 64 / 36 + 1) by (apply Z.div_lt_upper_bound; lia).
    lia.
  - ring.
Qed.

Lemma geo_word : forall len, 52 <= len < 2 ^ 64 ->
  le4 (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned (v_sltu (Z_to_bv 64 0)
        (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (len + -52)) -
                     bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 ((len + -52) / 36)) * 36))))) + -1)))
      (bv_unsigned (Z_to_bv 64 ((len + -52) / 36))))) = le4 (Z_to_bv 64 (geo len)).
Proof.
  intros len Hl.
  assert (Q0 : 0 <= (len + -52) / 36 < 2 ^ 64) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  assert (Q1 : 0 <= (len + -52) / 36 * 36 <= len + -52) by (pose proof (Z.mul_div_le (len + -52) 36); lia).
  rewrite v_sltu_b2z.
  rewrite (unsigned_lit (len + -52)), (unsigned_lit ((len + -52) / 36)) by lia.
  rewrite (unsigned_lit ((len + -52) / 36 * 36)) by lia.
  rewrite (unsigned_lit (len + -52 - (len + -52) / 36 * 36)) by lia.
  rewrite (unsigned_lit 0) by lia.
  assert (EM : len + -52 - (len + -52) / 36 * 36 = (len - 52) mod 36) by (rewrite Z.mod_eq by lia; lia).
  rewrite EM. replace (len + -52) with (len - 52) in * by lia.
  unfold geo. replace (52 <=? len) with true by (symmetry; apply Z.leb_le; lia). cbn [andb].
  destruct (Z.eqb_spec ((len - 52) mod 36) 0) as [E|E].
  - rewrite E. cbn [Z.ltb Z.compare Z.b2z]. rewrite (unsigned_lit 0) by lia.
    rewrite (unsigned_lit_wrap (0 + -1)). change ((0 + -1) mod 2 ^ 64) with (Z.ones 64).
    rewrite Z.land_comm, Z.land_ones by lia. rewrite Z.mod_small by lia.
    unfold le4. rewrite !unsigned_lit; [| pose proof (Z.mod_pos_bound ((len - 52) / 36) (2^32)); lia | lia].
    symmetry. apply (Z_to_le_bytes_mod 4 _ 32). cbn. lia.
  - pose proof (Z.mod_pos_bound (len - 52) 36). replace (0 <? (len - 52) mod 36) with true by (symmetry; apply Z.ltb_lt; lia).
    cbn [Z.b2z]. rewrite (unsigned_lit 1) by lia. change (1 + -1) with 0. rewrite (unsigned_lit 0) by lia.
    rewrite Z.land_0_l. reflexivity.
Qed.

Lemma cc_merge : forall m A cs Y n, rw_cells rsegs m A cs -> cells_bytes cs = Y -> cells_size cs = n ->
  rw_cells rsegs m A [CB n Y].
Proof.
  intros m A cs Y n H EY En.
  assert (H' : rw_cells rsegs m A ([] ++ cs ++ [])) by (rewrite app_nil_r; exact H).
  apply rw_cells_merge in H'. cbn [app] in H'. rewrite EY, En in H'. exact H'.
Qed.

Lemma cc_post_trans : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 m lo o r OUT ms',
  munch [(bv_unsigned sp - 192, bv_unsigned sp); (o, o + 24)] m0 m -> wmono rsegs m0 m ->
  cc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo o r OUT ms' ->
  cc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 lo o r OUT ms'.
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 m lo o r OUT ms' MU WM
    (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & M & W & I & S & O).
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [exact E|]. split; [eapply munch_trans; eassumption|]. split; [eapply wmono_trans; eassumption|].
  split; [exact I|]. split; [exact S | exact O].
Qed.

Lemma src_len : forall F, length F = 50%nat -> length (src F) = 6%nat.
Proof. intros F HF. unfold src, fld. rewrite length_firstn, length_skipn, HF. reflexivity. Qed.

Lemma sbh_len : forall F r, length F = 50%nat -> length (sbh F r) = 12%nat.
Proof. intros F r HF. unfold sbh. rewrite !length_app, src_len, length_le4 by exact HF. reflexivity. Qed.

Lemma sbo_geo : forall F r d sl g g', length F = 50%nat -> length d = 3%nat ->
  firstn 20 (sbo F r d sl g) ++ le4 (Z_to_bv 64 g') ++ [] = sbo F r d sl g'.
Proof.
  intros F r d sl g g' HF Hd. unfold sbo. rewrite app_nil_r.
  replace 20%nat with (length (sbh F r ++ d ++ [zb 0; zb sl; zb 0; zb 0; zb 0])) by (rewrite !length_app, sbh_len, Hd by exact HF; reflexivity).
  rewrite !app_assoc, firstn_app_exact. reflexivity.
Qed.

Lemma cc_geo : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (sp0 vra v0 v1 v2 v3 v4 v5 v6 : word) (lo o len : Z)
    (FB : list byte) (r : Z) (d : list byte) (sl : Z) (cw cq : list cell),
  sp = Z_to_bv 64 (bv_unsigned sp0 + -112) -> s0 = Z_to_bv 64 o -> s1 = Z_to_bv 64 len ->
  rw_cells rsegs m o [CB 24 (sbo FB r d sl 0)] -> stk rsegs m lo (bv_unsigned sp0 + -112) ->
  rw_cells rsegs m (bv_unsigned sp0 + -64) [C8 v6; C8 v5; C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 vra] ->
  rw_cells rsegs m (bv_unsigned sp0 + -112) cw -> rw_cells rsegs m (bv_unsigned sp0 + -100) cq ->
  lo + 192 <= bv_unsigned sp0 -> 0 <= len < 2 ^ 64 -> length FB = 50%nat -> length d = 3%nat ->
  (o + 24 <= bv_unsigned sp0 - 192 \/ bv_unsigned sp0 <= o) ->
  cells_size cw = 12%nat -> cells_size cq = 36%nat -> mem_inv rsegs m ->
  evt rsegs (cc_post vra sp0 gp tp v0 v1 v2 v3 v4 v5 v6 s7 s8 s9 s10 s11 F fc m lo o 0 (sbo FB r d sl (geo len)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15638) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m sp0
    vra v0 v1 v2 v3 v4 v5 v6 lo o len FB r d sl cw cq Esp Es0 Es1 HO ST SV HW HQ LO Hlen HFl Hd HOd Hw Hq HI.
  subst sp s0 s1.
  pose proof (bv_unsigned_in_range 64 sp0) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof ST as (Slo & Shi & _).
  pose proof (rw_cells_bound rsegs m o _ HO) as HOb. cbn [cells_size csize] in HOb.
  pose proof (munch_refl [(bv_unsigned sp0 - 192, bv_unsigned sp0); (o, o + 24)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. step.
  if_cases HC.
  - zify_cond HC.
    do 4 step.
    rewrite (unsigned_lit (len + -52)) by lia.
    step.
    rewrite (kq_div (len + -52)) by lia.
    do 8 step.
    eapply evt_mono.
    { apply cc_merge with (Y := sbo FB r d sl (geo len)) (n := 24%nat) in HO; [| | reflexivity].
      - eapply cc_exit; [reflexivity | exact LO | exact ST | exact HW | exact Hw | exact HQ | exact Hq | exact SV | exact HO | exact HI].
      - cbn [cells_bytes cbytes]. rewrite geo_word by lia. apply sbo_geo; assumption. }
    intros ms' P. eapply cc_post_trans; eassumption.
  - zify_cond HC.
    do 4 step.
    eapply evt_mono.
    { apply cc_merge with (Y := sbo FB r d sl (geo len)) (n := 24%nat) in HO; [| | reflexivity].
      - eapply cc_exit; [reflexivity | exact LO | exact ST | exact HW | exact Hw | exact HQ | exact Hq | exact SV | exact HO | exact HI].
      - cbn [cells_bytes cbytes].
        replace (geo len) with 0 by (unfold geo; replace (52 <=? len) with false by (symmetry; apply Z.leb_gt; lia); reflexivity).
        apply sbo_geo; assumption. }
    intros ms' P. eapply cc_post_trans; eassumption.
Qed.

Lemma cnt_range : forall g bs k, 0 <= cnt g bs k <= Z.of_nat k.
Proof. intros g bs k. induction k as [|k IH]; cbn [cnt]; [lia|]. destruct (g _); lia. Qed.

Lemma n_in_range : forall bs, 0 <= n_in bs <= 12.
Proof. intros bs. exact (cnt_range is_in bs 12). Qed.
Lemma n_out_range : forall bs, 0 <= n_out bs <= 12.
Proof. intros bs. exact (cnt_range is_out bs 12). Qed.

Lemma sx32_small : forall z, 0 <= z < 2 ^ 31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. rewrite unsigned_lit by lia. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  rewrite Z.mod_small by lia. f_equal. lia.
Qed.

Lemma zxb_small : forall z, 0 <= z < 256 -> Z_to_bv 64 z = zxb (zb z).
Proof.
  intros z Hz. unfold zxb, zb. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 8) with 256. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma le1_z : forall z, le1 (Z_to_bv 64 z) = [zb z].
Proof.
  intros z. unfold le1, zb. cbn [Z_to_le_bytes]. rewrite unsigned_lit_wrap. f_equal. apply bv_eq.
  rewrite !Z_to_bv_unsigned. change (bv_wrap 8 ?a) with (a mod 2 ^ 8). Z.div_mod_to_equations. lia.
Qed.

Lemma bytes_sub : forall m A (bs : list byte) k n, bytes_at rsegs m A bs -> (k + n <= length bs)%nat ->
  bytes_at rsegs m (A + Z.of_nat k) (firstn n (skipn k bs)).
Proof.
  intros m A bs k n H Hk.
  rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite firstn_length_le in H by lia.
  rewrite <- (firstn_skipn n (skipn k bs)) in H. apply bytes_at_app in H. destruct H as [H _]. exact H.
Qed.

Lemma c4x3 : forall m A a b c, bytes_at rsegs m A (le4 a) -> bytes_at rsegs m (A + 4) (le4 b) ->
  bytes_at rsegs m (A + 8) (le4 c) -> wr_at rsegs m A 12 -> rw_cells rsegs m A [C4 a; C4 b; C4 c].
Proof.
  intros m A a b c H0 H4 H8 HW. split; [split; [cbn; tauto|] | exact HW].
  cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_app. split; [exact H0|]. rewrite length_le4.
  apply bytes_at_app. split; [exact H4|]. rewrite length_le4. replace (A + Z.of_nat 4 + Z.of_nat 4) with (A + 8) by lia.
  exact H8.
Qed.

Ltac fix_ret :=
  try (lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end).

Lemma app12 : forall (A B : list byte) k, length A = 12%nat ->
  firstn 12 (A ++ B) = A /\ skipn (12 + k) (A ++ B) = skipn k B.
Proof.
  intros A B k HA. rewrite <- HA. split; [apply firstn_app_exact|]. rewrite skipn_app, skipn_all2 by lia.
  cbn [app]. f_equal. lia.
Qed.

Lemma sbo_decl : forall F r sl a b, length F = 50%nat ->
  firstn 12 (sbo F r [zb 0; zb 0; zb 0] sl 0) ++ [zb 1] ++ [zb a] ++ [zb b]
    ++ skipn 1 (skipn 1 (skipn 13 (sbo F r [zb 0; zb 0; zb 0] sl 0))) ++ [] = sbo F r [zb 1; zb a; zb b] sl 0.
Proof.
  intros F r sl a b HF. unfold sbo.
  destruct (app12 (sbh F r) ([zb 0; zb 0; zb 0] ++ [zb 0; zb sl; zb 0; zb 0; zb 0] ++ le4 (Z_to_bv 64 0)) 1
    (sbh_len F r HF)) as [E1 E2].
  cbn [Nat.add] in E2. rewrite E1, E2. cbn [skipn app]. rewrite app_nil_r. reflexivity.
Qed.

Ltac to_geo dd :=
  eapply evt_mono;
  [ eapply cc_geo with (d := dd);
    [ reflexivity | reflexivity | reflexivity | eassumption | eassumption | eassumption | eassumption | eassumption
    | assumption | assumption | assumption | reflexivity | assumption
    | first [assumption | reflexivity] | first [assumption | reflexivity] | assumption ]
  | intros ?ms' ?P; eapply cc_post_trans; eassumption ].

Lemma cc_ports : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (sp0 vra v0 v1 v2 v3 v4 v5 v6 : word) (lo o len f : Z)
    (FB wj : list byte) (r sl : Z) (cq : list cell),
  reac_ports_parse_contract ->
  sp = Z_to_bv 64 (bv_unsigned sp0 + -112) -> s0 = Z_to_bv 64 o -> s1 = Z_to_bv 64 len -> s2 = Z_to_bv 64 f ->
  a0 = Z_to_bv 64 (f + 18) ->
  bv_unsigned sp0 mod 16 = 0 -> lo + 192 <= bv_unsigned sp0 -> 0 <= len < 2 ^ 64 -> length FB = 50%nat ->
  0 < f -> bytes_at rsegs m f FB ->
  (f + 50 <= bv_unsigned sp0 - 192 \/ bv_unsigned sp0 <= f) ->
  (o + 24 <= bv_unsigned sp0 - 192 \/ bv_unsigned sp0 <= o) -> (o + 24 <= f \/ f + 50 <= o) ->
  stk rsegs m lo (bv_unsigned sp0 + -112) ->
  rw_cells rsegs m (bv_unsigned sp0 + -112) [CB 12 wj] ->
  rw_cells rsegs m (bv_unsigned sp0 + -100) cq -> cells_size cq = 36%nat ->
  rw_cells rsegs m (bv_unsigned sp0 + -64) [C8 v6; C8 v5; C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 vra] ->
  rw_cells rsegs m o [CB 24 (sbo FB r [zb 0; zb 0; zb 0] sl 0)] -> mem_inv rsegs m ->
  evt rsegs (cc_post vra sp0 gp tp v0 v1 v2 v3 v4 v5 v6 s7 s8 s9 s10 s11 F fc m lo o 0 (sbo FB r (dbytes FB) sl (geo len)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15600) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m sp0
    vra v0 v1 v2 v3 v4 v5 v6 lo o len f FB wj r sl cq PP Esp Es0 Es1 Es2 Ea0 S16 LO Hlen HFl Hf0 HFB HFd HOd HOF
    ST HW HQ Hq SV HO HI.
  subst sp s0 s1 s2 a0.
  pose proof (bv_unsigned_in_range 64 sp0) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof ST as (Slo & Shi & _).
  pose proof (rw_cells_bound rsegs m o _ HO) as HOb. cbn [cells_size csize] in HOb.
  pose proof (bytes_at_bound rsegs m f FB HFB) as HFb. rewrite HFl in HFb. change (Z.of_nat 50) with 50 in HFb.
  pose proof (bytes_sub m f FB 18 20 HFB ltac:(lia)) as HP. change (f + Z.of_nat 18) with (f + 18) in HP.
  pose proof (munch_refl [(bv_unsigned sp0 - 192, bv_unsigned sp0); (o, o + 24)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. step. if_cases HC; zify_cond HC; [exfalso; lia|].
  step. step.
  pose proof (proj2 HW) as HWr. change (Z.of_nat (cells_size [CB 12 wj])) with 12 in HWr.
  eapply evt_cut.
  { eapply PP with (p := f + 18) (q := bv_unsigned sp0 + -112) (bs := fld FB 18 20).
    - reflexivity.
    - reflexivity.
    - lia.
    - lia.
    - intros _ _; split; [unfold fld; rewrite length_firstn, length_skipn, HFl; reflexivity | exact HP].
    - intros _ _; split; [Z.div_mod_to_equations; lia | split; [exact HWr | lia]]. }
  intros ms' (t0' & t1' & a2' & a3' & a4' & a5' & a6' & a7' & m' & E & PO). subst ms'.
  assert (PK : ports_ok (f + 18) (bv_unsigned sp0 + -112) (fld FB 18 20) = decl (fld FB 18 20))
    by (unfold ports_ok; rewrite (proj2 (Z.eqb_neq (f + 18) 0)), (proj2 (Z.eqb_neq _ 0)) by lia; reflexivity).
  rewrite PK in PO |- *. fix_ret.
  pose proof (n_in_range (fld FB 18 20)) as RI. pose proof (n_out_range (fld FB 18 20)) as RO.
  destruct (decl (fld FB 18 20)) eqn:PD.
  - destruct PO as (B0 & B4 & B8 & MUc & WMc & MIc). specialize (MIc HI).
    transport_after_call rsegs m m' MUc WMc. clear MUc WMc HI.
    pose proof (c4x3 m' _ _ _ _ B0 B4 B8 HWr) as HW. clear B0 B4 B8.
    step. if_cases HC1; zify_cond HC1; [exfalso; lia|].
    step. rewrite sx32_small by lia.
    step. step. if_cases HC2; zify_cond HC2.
    + replace (dbytes FB) with [zb 0; zb 0; zb 0]
        by (unfold dbytes, sdecl; rewrite PD; replace (4 * n_in (fld FB 18 20) <=? 40) with false by (symmetry; apply Z.leb_gt; lia); reflexivity).
      to_geo [zb 0; zb 0; zb 0].
    + step. rewrite sx32_small by lia.
      step. if_cases HC3; zify_cond HC3.
      * replace (dbytes FB) with [zb 0; zb 0; zb 0]
          by (unfold dbytes, sdecl; rewrite PD; replace (4 * n_out (fld FB 18 20) <=? 40) with false by (symmetry; apply Z.leb_gt; lia);
              rewrite andb_false_r; reflexivity).
        to_geo [zb 0; zb 0; zb 0].
      * step. step. rewrite le1_z. mem_after_store.
        step. rewrite le1_z. mem_after_store.
        step. rewrite le1_z. mem_after_store.
        apply cc_merge with (Y := sbo FB r [zb 1; zb (4 * n_in (fld FB 18 20)); zb (4 * n_out (fld FB 18 20))] sl 0)
          (n := 24%nat) in HO; [| cbn [cells_bytes cbytes]; apply sbo_decl; exact HFl | reflexivity].
        replace (dbytes FB) with [zb 1; zb (4 * n_in (fld FB 18 20)); zb (4 * n_out (fld FB 18 20))]
          by (unfold dbytes, sdecl; rewrite PD; replace (4 * n_in (fld FB 18 20) <=? 40) with true by (symmetry; apply Z.leb_le; lia);
              replace (4 * n_out (fld FB 18 20) <=? 40) with true by (symmetry; apply Z.leb_le; lia); reflexivity).
        to_geo [zb 1; zb (4 * n_in (fld FB 18 20)); zb (4 * n_out (fld FB 18 20))].
  - subst m'. step. if_cases HC1; zify_cond HC1; [|exfalso; lia].
    replace (dbytes FB) with [zb 0; zb 0; zb 0] by (unfold dbytes, sdecl; rewrite PD; reflexivity).
    to_geo [zb 0; zb 0; zb 0].
Qed.

Lemma skipn_cons_nth : forall (F : list byte) k d, (k < length F)%nat -> skipn k F = nth k F d :: skipn (S k) F.
Proof. induction F as [|x F IH]; intros [|k] d H; cbn in *; try lia; [reflexivity|]. apply IH. lia. Qed.

Lemma fld_nth : forall (F : list byte) n k, (k + n <= length F)%nat -> fld F k n = map (fun i => nth i F (zb 0)) (seq k n).
Proof.
  unfold fld. intros F n. induction n as [|n IH]; intros k H; [reflexivity|].
  rewrite (skipn_cons_nth F k (zb 0)) by lia. cbn [firstn seq map]. f_equal. apply IH. lia.
Qed.

Lemma le4_small : forall k, 0 <= k < 256 -> le4 (Z_to_bv 64 k) = [zb k; zb 0; zb 0; zb 0].
Proof.
  intros k Hk. unfold le4. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes].
  replace (Z.shiftr k 8) with 0 by (rewrite Z.shiftr_div_pow2 by lia; rewrite Z.div_small by lia; reflexivity).
  reflexivity.
Qed.

Lemma tag_range : forall F, 0 <= tag F < 65536.
Proof.
  intros F. unfold tag, fb. pose proof (byte_range (nth 34 F (zb 0))). pose proof (byte_range (nth 35 F (zb 0))). lia.
Qed.

Lemma le2_tag : forall F, le2 (Z_to_bv 64 (tag F)) = [cp_b F 35; cp_b F 34].
Proof.
  intros F. pose proof (tag_range F) as TR. unfold le2. rewrite unsigned_lit by lia. unfold tag, fb, zb, cp_b, cp_z in *.
  pose proof (byte_range (nth 34 F (Z_to_bv 8 0))). pose proof (byte_range (nth 35 F (Z_to_bv 8 0))).
  cbn [Z_to_le_bytes]. rewrite Z.shiftr_div_pow2 by lia.
  f_equal; [|f_equal]; apply bv_eq; rewrite Z_to_bv_unsigned; change (bv_wrap 8 ?x) with (x mod 2 ^ 8);
    Z.div_mod_to_equations; lia.
Qed.

Definition qcells (F : list byte) (n : Z) : list cell :=
  [C4 (Z_to_bv 64 (dkind F n)); CB 4 (fld F 6 4); CB 2 (fld F 10 2); CB 6 (fld F 0 6);
   C4 (Z_to_bv 64 (if cp_bcast F then 1 else 0));
   CB 6 [cp_b F 14; cp_b F 15; cp_b F 18; cp_b F 19; cp_b F 21; cp_b F 20];
   CB 1 [cp_b F 22]; CB 1 [cp_z];
   C2 (Z_to_bv 64 (if cp_rec F then tag F else 0));
   CB 6 ((if dkind F n =? 6 then [cp_b F 36; cp_b F 37; cp_b F 38] else [cp_z; cp_z; cp_z]) ++ [cp_z; cp_z; cp_z])].

Lemma qcells_ok : forall m A n F, length F = 50%nat -> cp_hdr n F = true ->
  rw_cells rsegs m A [CB 36 (snd (ctrlparse n F))] -> rw_cells rsegs m A (qcells F n).
Proof.
  intros m A n F HL HD [[_ HB] HW].
  assert (WF : cells_wf (qcells F n)).
  { unfold qcells. cbn [cells_wf cell_wf]. unfold fld. rewrite !length_firstn, !length_skipn, HL.
    destruct (cp_rec F), (dkind F n =? 6); repeat split. }
  assert (EB : cells_bytes (qcells F n) = snd (ctrlparse n F)).
  { unfold qcells, dkind, ctrlparse. rewrite HD. cbn [fst snd cells_bytes cbytes].
    pose proof (cp_kind_range F) as KR.
    rewrite (fld_nth F 4 6), (fld_nth F 2 10), (fld_nth F 6 0) by lia.
    rewrite le4_small by lia.
    replace (le4 (Z_to_bv 64 (if cp_bcast F then 1 else 0))) with [if cp_bcast F then Z_to_bv 8 1 else cp_z; cp_z; cp_z; cp_z]
      by (destruct (cp_bcast F); rewrite le4_small by lia; reflexivity).
    replace (le2 (Z_to_bv 64 (if cp_rec F then tag F else 0))) with (if cp_rec F then [cp_b F 35; cp_b F 34] else [cp_z; cp_z])
      by (destruct (cp_rec F); [symmetry; apply le2_tag | reflexivity]).
    unfold cp_struct. cbn [cells_bytes cbytes seq map app]. destruct (cp_rec F), (cp_kind F =? 6); reflexivity. }
  split; [split; [exact WF | rewrite EB; cbn [cells_bytes cbytes] in HB; rewrite app_nil_r in HB; exact HB] | exact HW].
Qed.

Lemma q_src : forall m A F n, length F = 50%nat -> rw_cells rsegs m A (qcells F n) -> bytes_at rsegs m (A + 4) (src F).
Proof.
  intros m A F n HL [[_ HB] _]. unfold qcells in HB. cbn [cells_bytes cbytes] in HB.
  apply bytes_at_app in HB as [_ HB]. rewrite length_le4 in HB. rewrite app_assoc in HB.
  apply bytes_at_app in HB as [HB _].
  replace (src F) with (fld F 6 4 ++ fld F 10 2) by (unfold src; rewrite !fld_nth by (rewrite HL; lia); reflexivity).
  exact HB.
Qed.

Lemma cc_parse : reac_ctrl_parse_contract ->
  forall (Q : machine_state -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (sp0 : word) (f len : Z) (FB qj : list byte),
  sp = Z_to_bv 64 (bv_unsigned sp0 + -112) -> a0 = Z_to_bv 64 f -> a1 = Z_to_bv 64 len ->
  a2 = Z_to_bv 64 (bv_unsigned sp0 + -100) ->
  bv_unsigned sp0 mod 16 = 0 -> 192 <= bv_unsigned sp0 -> 0 <= f < 2 ^ 64 -> 0 <= len < 2 ^ 64 -> length FB = 50%nat ->
  (50 <= len -> 0 < f /\ bytes_at rsegs m f FB /\ (f + 50 <= bv_unsigned sp0 - 192 \/ bv_unsigned sp0 <= f)) ->
  stk rsegs m (bv_unsigned sp0 + -192) (bv_unsigned sp0 + -112) ->
  rw_cells rsegs m (bv_unsigned sp0 + -100) [CB 36 qj] -> mem_inv rsegs m ->
  (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte) (cq : list cell),
     munch [(bv_unsigned sp0 + -100, bv_unsigned sp0 + -64); (bv_unsigned sp0 + -192, bv_unsigned sp0 + -112)] m m' ->
     wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' (bv_unsigned sp0 + -192) (bv_unsigned sp0 + -112) ->
     rw_cells rsegs m' (bv_unsigned sp0 + -100) cq -> cells_size cq = 36%nat ->
     (dkind FB len <> 0 -> cq = qcells FB len) ->
     evt rsegs Q (MS (mkR (Z_to_bv 64 0x15434) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (dkind FB len))
                        a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (Z_to_bv 64 0x15434) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x15430) fc None m (seg_rom rsegs)).
Proof.
  intros CP Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m sp0
    f len FB qj Esp Ea0 Ea1 Ea2 S16 S192 Hf Hlen HFl HF ST HQ HI K.
  subst sp a0 a1 a2.
  pose proof (bv_unsigned_in_range 64 sp0) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  step.
  eapply evt_cut.
  { eapply CP with (f := f) (n := len) (o := bv_unsigned sp0 + -100) (S := bv_unsigned sp0 + -112) (fr := FB) (junk := qj).
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - exact Hf.
    - exact Hlen.
    - lia.
    - lia.
    - Z.div_mod_to_equations. lia.
    - unfold REAC_CTRL_PARSE_K. lia.
    - unfold REAC_CTRL_PARSE_K. replace (bv_unsigned sp0 + -112 - 80) with (bv_unsigned sp0 + -192) by lia. exact ST.
    - exact HI.
    - exact HFl.
    - intros Hn. destruct (HF Hn) as (Hf0 & HFB & HFd). pose proof (bytes_at_bound rsegs m f FB HFB) as Hb.
      rewrite HFl in Hb. change (Z.of_nat 50) with 50 in Hb. unfold REAC_CTRL_PARSE_K. lia.
    - intros i Hi. destruct (Z.leb_spec 50 len) as [Hn|Hn].
      + destruct (HF Hn) as (_ & (_ & _ & HB) & _). apply HB. pose proof (cp_rd_lt39 len FB i Hi). rewrite HFl. lia.
      + unfold cp_rd in Hi. rewrite (proj2 (Z.leb_gt 50 len) Hn) in Hi. destruct Hi.
    - intros _. split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; [exact HQ|].
      split; [unfold REAC_CTRL_PARSE_K; lia|]. intros Hn. destruct (HF Hn) as (_ & _ & HFd). lia. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MUc & WMc & MIc & STc & RQ).
  subst ms'. fix_ret.
  specialize (RQ ltac:(lia)).
  unfold reac_ctrl_parse_fp, REAC_CTRL_PARSE_K in MUc.
  rewrite (proj2 (Z.eqb_neq (bv_unsigned sp0 + -100) 0)) in MUc by lia. cbn [app] in MUc.
  unfold REAC_CTRL_PARSE_K in STc. replace (bv_unsigned sp0 + -112 - 80) with (bv_unsigned sp0 + -192) in STc by lia.
  assert (MU' : munch [(bv_unsigned sp0 + -100, bv_unsigned sp0 + -64); (bv_unsigned sp0 + -192, bv_unsigned sp0 + -112)] m m').
  { eapply munch_weaken; [|exact MUc]. unfold sub_fp. cbn [outside]. intros x Hx. lia. }
  destruct (Z.eq_dec (dkind FB len) 0) as [K0|K0].
  - eapply K; [exact MU' | exact WMc | exact MIc | exact STc | exact RQ | reflexivity | intros C; contradiction].
  - assert (HD : cp_hdr len FB = true).
    { destruct (cp_hdr len FB) eqn:E; [reflexivity|]. exfalso. apply K0. unfold dkind, ctrlparse. rewrite E. reflexivity. }
    eapply K; [exact MU' | exact WMc | exact MIc | exact STc | apply (qcells_ok m' _ len FB); [exact HFl | exact HD | exact RQ]
              | reflexivity | intros _; reflexivity].
Qed.

Lemma le1_zxbb : forall b : byte, le1 (zxb b) = [b].
Proof. exact le1_zxb. Qed.

Lemma cc_zbu : forall b : byte, zb (bv_unsigned b) = b.
Proof. intros b. unfold zb. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma cc_zxbu : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b.
Proof. intros b. unfold zxb. apply unsigned_lit. pose proof (byte_range b). lia. Qed.

Lemma le_bytes_to_word2 : forall b0 b1 : byte,
  bv_unsigned (le_bytes_to_word [b0; b1]) = bv_unsigned b0 + 256 * bv_unsigned b1.
Proof.
  intros. unfold le_bytes_to_word. rewrite bytes_le_to_Z_le_val. cbn [map le_val].
  pose proof (byte_range b0). pose proof (byte_range b1). rewrite unsigned_lit by lia. lia.
Qed.

Lemma le2_lh : forall w : list byte, length w = 2%nat -> le2 (sext 64 (bv_extract 0 16 (le_bytes_to_word w))) = w.
Proof.
  intros w Hl. destruct w as [|b0 [|b1 [|]]]; try (cbn in Hl; discriminate).
  pose proof (byte_range b0). pose proof (byte_range b1).
  assert (SW : forall z, bv_swrap 16 z = (z + 2 ^ 15) mod 2 ^ 16 - 2 ^ 15) by reflexivity.
  unfold le2. rewrite <- (Z_to_le_bytes_mod 2 _ 16) by (cbn; lia).
  rewrite sext_small, Z_to_bv_unsigned, signed_of_extract, le_bytes_to_word2 by reflexivity.
  replace (bv_wrap 64 (bv_swrap 16 (bv_unsigned b0 + 256 * bv_unsigned b1)) mod 2 ^ 16) with (bytes_le_to_Z [b0; b1]).
  - change 2%nat with (length [b0; b1]). apply Z_to_le_bytes_to_Z.
  - rewrite bytes_le_to_Z_le_val. cbn [map le_val]. rewrite SW. change (bv_wrap 64 ?x) with (x mod 2 ^ 64).
    Z.div_mod_to_equations. lia.
Qed.

Lemma lhu_tag : forall b0 b1 : byte,
  bv_unsigned (zext 64 (bv_extract 0 16 (le_bytes_to_word [b0; b1]))) = bv_unsigned b0 + 256 * bv_unsigned b1.
Proof.
  intros. pose proof (byte_range b0). pose proof (byte_range b1).
  rewrite zext_small, extract_low_mod, le_bytes_to_word2 by reflexivity.
  rewrite unsigned_lit; [apply Z.mod_small|]; cbn; lia.
Qed.

Lemma src_split : forall F, length F = 50%nat -> src F = fld F 6 4 ++ fld F 10 2.
Proof. intros F HL. unfold src. rewrite !fld_nth by (rewrite HL; lia). reflexivity. Qed.

Lemma src_lw : forall F, length F = 50%nat ->
  le4 (sext 64 (bv_extract 0 32 (le_bytes_to_word (fld F 6 4))))
  ++ le2 (sext 64 (bv_extract 0 16 (le_bytes_to_word (fld F 10 2)))) = src F.
Proof.
  intros F HL.
  rewrite le4_lw, le2_lh, (src_split F HL) by (unfold fld; rewrite length_firstn, length_skipn, HL; reflexivity).
  reflexivity.
Qed.

Lemma sight_sbo : forall F len, sight F len = sbo F (role F (dkind F len)) (dbytes F) (slots F) (geo len).
Proof. intros. unfold sight, sbo, sbh, dbytes. rewrite <- !app_assoc. reflexivity. Qed.

Lemma role_range : forall F k, 0 <= role F k <= 2.
Proof. intros F k. unfold role. repeat match goal with |- context [if ?c then _ else _] => destruct c end; lia. Qed.

Lemma role5 : forall F, role F 5 = if (fb F 22 =? 0) && ((tag F =? 256) || (tag F =? 770) || (tag F =? 1280)) then 1 else 2.
Proof. reflexivity. Qed.

Lemma cc_slot0 : forall F,
  ~ (bv_unsigned (nth 16 F (Z_to_bv 8 0)) = 207 /\ bv_unsigned (nth 17 F (Z_to_bv 8 0)) = 234 /\
     bv_unsigned (nth 22 F (Z_to_bv 8 0)) = 1 /\ bv_unsigned (nth 23 F (Z_to_bv 8 0)) = 3 /\
     bv_unsigned (nth 24 F (Z_to_bv 8 0)) = 13 /\ bv_unsigned (nth 25 F (Z_to_bv 8 0)) = 1 /\
     bv_unsigned (nth 26 F (Z_to_bv 8 0)) = 4) -> slots F = 0.
Proof.
  intros F H. unfold slots, fb, zb.
  destruct (_ && _) eqn:E; [|reflexivity]. exfalso. apply H. rewrite !andb_true_iff, !Z.eqb_eq in E. tauto.
Qed.

Lemma cc_slot1 : forall F, bv_unsigned (nth 16 F (Z_to_bv 8 0)) = 207 -> bv_unsigned (nth 17 F (Z_to_bv 8 0)) = 234 ->
  bv_unsigned (nth 22 F (Z_to_bv 8 0)) = 1 -> bv_unsigned (nth 23 F (Z_to_bv 8 0)) = 3 ->
  bv_unsigned (nth 24 F (Z_to_bv 8 0)) = 13 -> bv_unsigned (nth 25 F (Z_to_bv 8 0)) = 1 ->
  bv_unsigned (nth 26 F (Z_to_bv 8 0)) = 4 -> slots F = fb F 33.
Proof. intros F H16 H17 H22 H23 H24 H25 H26. unfold slots, fb, zb. rewrite H16, H17, H22, H23, H24, H25, H26. reflexivity. Qed.

Definition ocells (x1 x2 : word) : list cell :=
  [C4 x1; C2 x2; CB 2 [zb 0; zb 0]; C4 (Z_to_bv 64 0); CB 3 [zb 0; zb 0; zb 0]; C1 (zb 0); C1 (zb 0);
   CB 3 [zb 0; zb 0; zb 0]; C4 (Z_to_bv 64 0)].

Lemma cc_obytes : forall FB x1 x2 r sl b, le4 x1 ++ le2 x2 = src FB -> b = zb sl ->
  cells_bytes [C4 x1; C2 x2; CB 2 [zb 0; zb 0]; C4 (Z_to_bv 64 r); CB 3 [zb 0; zb 0; zb 0]; C1 (zb 0); C1 b;
               CB 3 [zb 0; zb 0; zb 0]; C4 (Z_to_bv 64 0)] = sbo FB r [zb 0; zb 0; zb 0] sl 0.
Proof.
  intros FB x1 x2 r sl b HS ->. unfold sbo, sbh. rewrite <- HS. cbn [cells_bytes cbytes].
  rewrite app_nil_r, <- !app_assoc. reflexivity.
Qed.

Lemma stk_patch : forall m m' lo hi a n, stk rsegs m lo hi -> munch [(a, a + n)] m m' -> wmono rsegs m m' ->
  stk rsegs m' a (a + n) -> stk rsegs m' lo hi.
Proof.
  intros m m' lo hi a n (H1 & H2 & H) MU WM (_ & _ & G). split; [lia|]. split; [lia|].
  intros x Hx.
  assert (D : (a <= x < a + n) \/ ~ (a <= x < a + n)) by lia.
  destruct D as [D|D]; [apply G; exact D|].
  destruct (H x Hx) as [Hw (b & Hb)]. split; [apply WM; exact Hw|]. exists b. unfold mrd in *.
  rewrite MU; [exact Hb|]. cbn [outside]. rewrite wa_unsigned by lia. split; [exact D | exact I].
Qed.

Ltac to_ports PP FB sl0 :=
  lazymatch goal with
  | HO : rw_cells rsegs ?mm ?oo [C4 ?x1; C2 ?x2; CB 2 _; C4 (Z_to_bv 64 ?rr); CB 3 _; C1 _; C1 ?bb; CB 3 _; C4 _] |- _ =>
      apply cc_merge with (Y := sbo FB rr [zb 0; zb 0; zb 0] sl0 0) (n := 24%nat) in HO;
      [ | apply cc_obytes; [assumption | first [reflexivity | symmetry; apply cc_zbu]] | reflexivity ]
  end;
  eapply evt_mono;
  [ eapply cc_ports with (sl := sl0);
    [ exact PP | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
    | eassumption | eassumption | lia | eassumption | eassumption | eassumption | eassumption | eassumption
    | eassumption | eassumption | eassumption | eassumption | eassumption | eassumption | eassumption | eassumption ]
  | intros ?ms' ?P; eapply cc_post_trans; eassumption ].

Lemma cc_mid : reac_ports_parse_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (sp0 vra v0 v1 v2 v3 v4 v5 v6 : word) (lo o len f : Z)
    (FB wj : list byte) (r : Z) (x1 x2 : word) (cq : list cell),
  sp = Z_to_bv 64 (bv_unsigned sp0 + -112) -> s0 = Z_to_bv 64 o -> s1 = Z_to_bv 64 len -> s2 = Z_to_bv 64 f ->
  a0 = Z_to_bv 64 r -> 0 <= r <= 2 ->
  bv_unsigned sp0 mod 16 = 0 -> lo + 192 <= bv_unsigned sp0 -> 50 <= len < 2 ^ 64 -> length FB = 50%nat ->
  0 < f -> bytes_at rsegs m f FB ->
  (f + 50 <= bv_unsigned sp0 - 192 \/ bv_unsigned sp0 <= f) ->
  (o + 24 <= bv_unsigned sp0 - 192 \/ bv_unsigned sp0 <= o) -> (o + 24 <= f \/ f + 50 <= o) ->
  stk rsegs m lo (bv_unsigned sp0 + -112) ->
  rw_cells rsegs m (bv_unsigned sp0 + -112) [CB 12 wj] ->
  rw_cells rsegs m (bv_unsigned sp0 + -100) cq -> cells_size cq = 36%nat ->
  rw_cells rsegs m (bv_unsigned sp0 + -64) [C8 v6; C8 v5; C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 vra] ->
  le4 x1 ++ le2 x2 = src FB -> rw_cells rsegs m o (ocells x1 x2) -> mem_inv rsegs m ->
  evt rsegs (cc_post vra sp0 gp tp v0 v1 v2 v3 v4 v5 v6 s7 s8 s9 s10 s11 F fc m lo o 0
               (sbo FB r (dbytes FB) (slots FB) (geo len)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15548) fc None m (seg_rom rsegs)).
Proof.
  intros PP ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m sp0
    vra v0 v1 v2 v3 v4 v5 v6 lo o len f FB wj r x1 x2 cq Esp Es0 Es1 Es2 Ea0 Hr S16 LO Hlen HFl Hf0 HFB HFd HOd HOF
    ST HW HQ Hq SV HS HO HI.
  subst sp s0 s1 s2 a0. unfold ocells in HO.
  pose proof (bv_unsigned_in_range 64 sp0) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof ST as (Slo & Shi & _).
  pose proof (rw_cells_bound rsegs m o _ HO) as HOb. cbn [cells_size csize Nat.add] in HOb.
  pose proof (bytes_at_bound rsegs m f FB HFB) as HFb. rewrite HFl in HFb. change (Z.of_nat 50) with 50 in HFb.
  assert (Ulen : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; lia).
  assert (Uf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (Uf18 : bv_unsigned (Z_to_bv 64 (f + 18)) = f + 18) by (apply unsigned_lit; lia).
  pose proof (munch_refl [(bv_unsigned sp0 - 192, bv_unsigned sp0); (o, o + 24)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. step. step. if_false.
  step. if_false.
  step. step. if_false.
  pose proof (rd_byte rsegs _ f FB 16 HFB ltac:(lia)) as R16. change (f + Z.of_nat 16) with (f + 16) in R16.
  pose proof (rd_byte rsegs _ f FB 17 HFB ltac:(lia)) as R17. change (f + Z.of_nat 17) with (f + 17) in R17.
  pose proof (rd_byte rsegs _ f FB 22 HFB ltac:(lia)) as R22. change (f + Z.of_nat 22) with (f + 22) in R22.
  pose proof (rd_byte rsegs _ f FB 23 HFB ltac:(lia)) as R23. change (f + Z.of_nat 23) with (f + 23) in R23.
  pose proof (rd_byte rsegs _ f FB 24 HFB ltac:(lia)) as R24. change (f + Z.of_nat 24) with (f + 24) in R24.
  pose proof (rd_byte rsegs _ f FB 25 HFB ltac:(lia)) as R25. change (f + Z.of_nat 25) with (f + 25) in R25.
  pose proof (rd_byte rsegs _ f FB 26 HFB ltac:(lia)) as R26. change (f + Z.of_nat 26) with (f + 26) in R26.
  pose proof (rd_byte rsegs _ f FB 33 HFB ltac:(lia)) as R33. change (f + Z.of_nat 33) with (f + 33) in R33.
  pose proof (cc_zxbu (nth 16 FB (Z_to_bv 8 0))) as U16. pose proof (cc_zxbu (nth 17 FB (Z_to_bv 8 0))) as U17.
  pose proof (cc_zxbu (nth 22 FB (Z_to_bv 8 0))) as U22. pose proof (cc_zxbu (nth 23 FB (Z_to_bv 8 0))) as U23.
  pose proof (cc_zxbu (nth 24 FB (Z_to_bv 8 0))) as U24. pose proof (cc_zxbu (nth 25 FB (Z_to_bv 8 0))) as U25.
  pose proof (cc_zxbu (nth 26 FB (Z_to_bv 8 0))) as U26.
  step. step. step. step.
  destruct (Z.eq_dec (bv_unsigned (nth 16 FB (Z_to_bv 8 0))) 207) as [E16|E16];
    [if_false | if_true; rewrite (cc_slot0 FB) by lia; to_ports PP FB 0].
  step. step. if_false.
  step. step. step.
  destruct (Z.eq_dec (bv_unsigned (nth 17 FB (Z_to_bv 8 0))) 234) as [E17|E17];
    [if_false | if_true; rewrite (cc_slot0 FB) by lia; to_ports PP FB 0].
  step. step. if_false.
  step. step. if_false.
  step. step. step.
  destruct (Z.eq_dec (bv_unsigned (nth 22 FB (Z_to_bv 8 0))) 1) as [E22|E22];
    [if_false | if_true; rewrite (cc_slot0 FB) by lia; to_ports PP FB 0].
  step. step. if_false.
  step. step. step.
  destruct (Z.eq_dec (bv_unsigned (nth 23 FB (Z_to_bv 8 0))) 3) as [E23|E23];
    [if_false | if_true; rewrite (cc_slot0 FB) by lia; to_ports PP FB 0].
  step. step. if_false.
  step. step. step.
  destruct (Z.eq_dec (bv_unsigned (nth 24 FB (Z_to_bv 8 0))) 13) as [E24|E24];
    [if_false | if_true; rewrite (cc_slot0 FB) by lia; to_ports PP FB 0].
  step. step. if_false.
  step. step. step.
  destruct (Z.eq_dec (bv_unsigned (nth 25 FB (Z_to_bv 8 0))) 1) as [E25|E25];
    [if_false | if_true; rewrite (cc_slot0 FB) by lia; to_ports PP FB 0].
  step. step. if_false.
  step. step. step.
  destruct (Z.eq_dec (bv_unsigned (nth 26 FB (Z_to_bv 8 0))) 4) as [E26|E26];
    [if_false | if_true; rewrite (cc_slot0 FB) by lia; to_ports PP FB 0].
  step. step. if_false.
  step. step. rewrite le1_zxbb. mem_after_store.
  rewrite (cc_slot1 FB) by assumption.
  to_ports PP FB (fb FB 33).
Qed.

Ltac role5_tac :=
  rewrite role5;
  repeat match goal with
  | |- context [?a =? ?b] =>
      first [ replace (a =? b) with true by (symmetry; apply Z.eqb_eq; lia)
            | replace (a =? b) with false by (symmetry; apply Z.eqb_neq; lia) ]
  end; reflexivity.

Lemma cc_role : forall (Q : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (sp0 : word) (FB : list byte) (len : Z),
  sp = Z_to_bv 64 (bv_unsigned sp0 + -112) -> a3 = Z_to_bv 64 8 -> dkind FB len <> 0 ->
  rw_cells rsegs m (bv_unsigned sp0 + -100) (qcells FB len) -> mem_inv rsegs m ->
  (forall a0' a1' a2' : word, a0' = Z_to_bv 64 (role FB (dkind FB len)) ->
     evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                          t3 t4 t5 t6) F (Z_to_bv 64 0x15548) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (dkind FB len + -1)) a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x154fc) fc None m (seg_rom rsegs)).
Proof.
  intros Q ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m sp0 FB len
    Esp Ea3 Hk HQ HI K.
  subst sp a3.
  pose proof (bv_unsigned_in_range 64 sp0) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  unfold qcells in HQ.
  pose proof (rw_cells_bound rsegs m _ _ HQ) as HQb. cbn [cells_size csize Nat.add] in HQb.
  assert (RC : dkind FB len = 5 -> cp_rec FB = true)
    by (intros E; exact (proj1 (proj2 (ctrlparse_rec len FB (or_introl E))))).
  pose proof (ctrlparse_kind_range len FB) as KR. change (fst (ctrlparse len FB)) with (dkind FB len) in KR.
  remember (dkind FB len) as k eqn:Ek.
  assert (KC : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/
               k = 12 \/ k = 13) by lia.
  destruct KC as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| -> ]]]]]]]]]]]].
  - destruct (cp_bcast FB) eqn:BC.
    + step; if_false. do 8 step. do 3 step. apply K. unfold role. rewrite BC. reflexivity.
    + step; if_false. do 8 step. do 3 step. apply K. unfold role. rewrite BC. reflexivity.
  - step; if_false; do 8 step. apply K. reflexivity.
  - step; if_false; do 8 step. apply K. reflexivity.
  - step; if_false; do 8 step. apply K. reflexivity.
  - rewrite (RC eq_refl) in HQ; cbv iota in HQ.
    pose proof (cc_zxbu (cp_b FB 22)) as U22.
    assert (F22 : fb FB 22 = bv_unsigned (cp_b FB 22)) by reflexivity.
    assert (UT : bv_unsigned (zx16 (Z_to_bv 64 (tag FB))) = tag FB).
    { pose proof (tag_range FB). unfold zx16. rewrite (unsigned_lit (tag FB)) by lia. rewrite Z.mod_small by lia.
      apply unsigned_lit. lia. }
    step; if_false; do 8 step. step. step.
    destruct (Z.eq_dec (bv_unsigned (cp_b FB 22)) 0) as [E22|E22].
    + if_true. do 4 step.
      destruct (Z.eq_dec (tag FB) 256) as [T1|T1]; [if_true; apply K; f_equal; role5_tac | if_false].
      step; step.
      destruct (Z.eq_dec (tag FB) 770) as [T2|T2]; [if_true; apply K; f_equal; role5_tac | if_false].
      step; step.
      destruct (Z.eq_dec (tag FB) 1280) as [T3|T3].
      * if_false; step; apply K; f_equal; role5_tac.
      * if_true; step; step; apply K; f_equal; role5_tac.
    + if_false; step; step; apply K; f_equal; role5_tac.
  - step; if_false; do 8 step. apply K. reflexivity.
  - step; if_false; do 8 step; step; step. apply K. reflexivity.
  - step; if_false; do 8 step; step. apply K. reflexivity.
  - step; if_false; do 8 step; step; step. apply K. reflexivity.
  - step; if_true; step. apply K. reflexivity.
  - step; if_true; step. apply K. reflexivity.
  - step; if_true; step. apply K. reflexivity.
  - step; if_true; step. apply K. reflexivity.
Qed.

Lemma cc_oz : forall m o,
  rw_cells rsegs m o [CB (Z.to_nat (bv_unsigned (Z_to_bv 64 24)))
    (repeat (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0) mod 256)) (Z.to_nat (bv_unsigned (Z_to_bv 64 24))))] ->
  rw_cells rsegs m o (ocells (Z_to_bv 64 0) (Z_to_bv 64 0)).
Proof.
  intros m o [[_ HB] HW].
  assert (EB : cells_bytes (ocells (Z_to_bv 64 0) (Z_to_bv 64 0)) =
               cells_bytes [CB (Z.to_nat (bv_unsigned (Z_to_bv 64 24)))
                 (repeat (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0) mod 256)) (Z.to_nat (bv_unsigned (Z_to_bv 64 24))))])
    by (vm_compute; reflexivity).
  split; [split; [cbn; repeat split | rewrite EB; exact HB] | exact HW].
Qed.

Lemma cc_ms : memset_contract -> reac_ports_parse_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (sp0 vra v0 v1 v2 v3 v4 v5 v6 : word) (lo o len f : Z)
    (FB wj OB : list byte),
  sp = Z_to_bv 64 (bv_unsigned sp0 + -112) -> s0 = Z_to_bv 64 o -> s1 = Z_to_bv 64 len -> s2 = Z_to_bv 64 f ->
  s3 = Z_to_bv 64 (bv_unsigned sp0 + -96) -> dkind FB len <> 0 ->
  bv_unsigned sp0 mod 16 = 0 -> lo + 192 <= bv_unsigned sp0 -> 0 <= len < 2 ^ 64 -> length FB = 50%nat ->
  0 < f -> bytes_at rsegs m f FB -> (f + 50 <= bv_unsigned sp0 - 192 \/ bv_unsigned sp0 <= f) ->
  0 < o -> o mod 4 = 0 ->
  (o + 24 <= bv_unsigned sp0 - 192 \/ bv_unsigned sp0 <= o) -> (o + 24 <= f \/ f + 50 <= o) ->
  stk rsegs m lo (bv_unsigned sp0 + -112) ->
  rw_cells rsegs m (bv_unsigned sp0 + -112) [CB 12 wj] ->
  rw_cells rsegs m (bv_unsigned sp0 + -100) (qcells FB len) ->
  rw_cells rsegs m (bv_unsigned sp0 + -64) [C8 v6; C8 v5; C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 vra] ->
  rw_cells rsegs m o [CB 24 OB] -> mem_inv rsegs m ->
  evt rsegs (cc_post vra sp0 gp tp v0 v1 v2 v3 v4 v5 v6 s7 s8 s9 s10 s11 F fc m lo o 0 (sight FB len))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x154c4) fc None m (seg_rom rsegs)).
Proof.
  intros MS PP ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    sp0 vra v0 v1 v2 v3 v4 v5 v6 lo o len f FB wj OB Esp Es0 Es1 Es2 Es3 Hk S16 LO Hlen HFl Hf0 HFB HFd Ho0 Ho4 HOd HOF
    ST HW HQ SV HO HI.
  subst sp s0 s1 s2 s3.
  assert (L50 : 50 <= len).
  { destruct (Z_lt_le_dec len 50) as [C|C]; [|exact C]. exfalso. apply Hk. apply ctrlparse_none. intros [C' _]. lia. }
  pose proof (bv_unsigned_in_range 64 sp0) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof ST as (Slo & Shi & _).
  pose proof (rw_cells_bound rsegs m o _ HO) as HOb. cbn [cells_size csize Nat.add] in HOb.
  pose proof (bytes_at_bound rsegs m f FB HFB) as HFb. rewrite HFl in HFb. change (Z.of_nat 50) with 50 in HFb.
  pose proof (ctrlparse_kind_range len FB) as KR. change (fst (ctrlparse len FB)) with (dkind FB len) in KR.
  assert (U0 : bv_unsigned (Z_to_bv 64 o) = o) by (apply unsigned_lit; lia).
  assert (U24 : bv_unsigned (Z_to_bv 64 24) = 24) by reflexivity.
  assert (Ua : bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 o)) 3)) = 0).
  { rewrite U0. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2) with 4. rewrite Ho4. reflexivity. }
  unfold qcells in HQ.
  step; step; step; step.
  eapply evt_cut.
  { eapply MS; [rewrite U0; exact HO | exact HI]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & EQ & MU0 & WM0
    & MI0 & RC).
  subst ms'.
  rewrite U0, U24 in MU0. rewrite U0 in RC. apply cc_oz in RC.
  pose proof (stk_of_rw_cells rsegs m' o _ RC) as STo.
  change (Z.of_nat (cells_size (ocells (Z_to_bv 64 0) (Z_to_bv 64 0)))) with 24 in STo.
  pose proof (stk_patch m m' lo _ o 24 ST MU0 WM0 STo) as ST'. clear ST STo.
  transport_after_call rsegs m m' MU0 WM0.
  pose proof (munch_weaken [(o, o + 24)] [(bv_unsigned sp0 - 192, bv_unsigned sp0); (o, o + 24)] m m'
    ltac:(unfold sub_fp; intros x; cbn [outside]; tauto) MU0) as MU.
  clear MU0 HI. rename WM0 into WM. unfold ocells in RC.
  fix_ret.
  step; if_false.
  step; step; if_false.
  step. rewrite sx32_small by lia.
  step; step; step; step.
  step; step.
  rewrite (sight_sbo FB len).
  eapply cc_role; [reflexivity | reflexivity | exact Hk | exact HQ | assumption | ].
  intros a0' a1'' a2'' ->.
  eapply evt_mono.
  { eapply cc_mid; [exact PP | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | apply role_range
                   | exact S16 | exact LO | lia | exact HFl | exact Hf0 | eassumption | exact HFd | exact HOd | exact HOF
                   | eassumption | eassumption | eassumption | reflexivity | eassumption | apply src_lw; exact HFl
                   | eassumption | eassumption ]. }
  intros ms' P. eapply cc_post_trans; eassumption.
Qed.

Lemma cc_wr_split : forall m A n1 n2, wr_at rsegs m A (n1 + n2) -> 0 <= n1 -> 0 <= n2 ->
  wr_at rsegs m A n1 /\ wr_at rsegs m (A + n1) n2.
Proof.
  intros m A n1 n2 (H1 & H2 & H) P1 P2. split.
  - split; [lia|]. split; [lia|]. intros i Hi. apply H. lia.
  - split; [lia|]. split; [lia|]. intros i Hi. replace (A + n1 + i) with (A + (n1 + i)) by lia. apply H. lia.
Qed.

Lemma cc_rw_split : forall m A cs1 cs2,
  rw_cells rsegs m A (cs1 ++ cs2) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [[Hwf Hb] Hw].
  apply cells_wf_app in Hwf. destruct Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  rewrite cells_size_app, Nat2Z.inj_add in Hw.
  apply cc_wr_split in Hw; [| lia | lia]. destruct Hw as [V1 V2].
  rewrite cells_bytes_length in B2 by exact W1.
  split; (split; [split|]); assumption.
Qed.

Lemma cc_rw_split2 : forall m A cs1 cs2 B, rw_cells rsegs m A (cs1 ++ cs2) -> B = A + Z.of_nat (cells_size cs1) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m B cs2.
Proof. intros m A cs1 cs2 B H ->. apply cc_rw_split. exact H. Qed.

Lemma cc_rw_nil : forall m, rw_cells rsegs m 0 [CB 0 []].
Proof.
  intros m. split; [split|].
  - cbn. split; [reflexivity | exact I].
  - cbn. apply bytes_at_nil. lia.
  - cbn. split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

Lemma cc_rwb : forall m A n bs, rw_cells rsegs m A [CB n bs] -> bytes_at rsegs m A bs /\ length bs = n.
Proof.
  intros m A n bs [[[L _] B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. split; assumption.
Qed.

Lemma cc_rd : forall m a bs (k : Z) n, bytes_at rsegs m a bs -> 0 <= k -> (Z.to_nat k + n <= length bs)%nat ->
  ov_read_bytes rsegs m (Z_to_bv 64 (a + k)) n = Some (firstn n (skipn (Z.to_nat k) bs)).
Proof. intros m a bs k n H Hk Hn. exact (bytes_at_read rsegs m a bs k n H Hk Hn). Qed.

Lemma cc_lv0 : forall c, 0 <= c < 2 ^ 32 -> bv_eqb (Z_to_bv 64 (bv_swrap 32 c)) (Z_to_bv 64 0) = (c =? 0).
Proof.
  intros c Hc. unfold bv_eqb. rewrite !unsigned_lit_wrap. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  destruct (Z.eqb_spec c 0) as [->|N]; [reflexivity|].
  apply Z.eqb_neq. Z.div_mod_to_equations. lia.
Qed.

Lemma cc_fu4 : forall bs k, (k + 4 <= length bs)%nat -> 0 <= fu bs k 4 < 2 ^ 32.
Proof.
  intros bs k Hk. unfold fu, fld. pose proof (disco_table.ble_range (firstn 4 (skipn k bs))) as R.
  rewrite length_firstn, length_skipn in R. replace (Init.Nat.min 4 (length bs - k)) with 4%nat in R by lia.
  exact R.
Qed.

Lemma cc_beqb : forall a b, bytes_eqb a b = true <-> a = b.
Proof.
  intros a b. unfold bytes_eqb. destruct (list_eq_dec Z.eq_dec (map bv_unsigned a) (map bv_unsigned b)) as [E|E];
    split; intros H; try reflexivity; try discriminate.
  - revert b E. induction a as [|x a IH]; intros [|y b] E; cbn in E; try discriminate; [reflexivity|].
    injection E as E1 E2. f_equal; [apply bv_eq; exact E1 | apply IH; exact E2].
  - exfalso. apply E. subst b. reflexivity.
Qed.

Definition cc_L (L : option (list byte)) (lk lkA : Z) (nL : nat) (LKb : list byte) : Prop :=
  match L with
  | None => lk = 0 /\ lkA = 0 /\ nL = 0%nat /\ LKb = []
  | Some Lb => 0 < lk /\ lk mod 4 = 0 /\ lkA = lk /\ nL = 12%nat /\ LKb = Lb
  end.

Definition cc_lock (FB U : list byte) (len lk : Z) (L : option (list byte)) (lkA : Z) (nL : nat) (LKb : list byte)
    : Prop :=
  match cm_lock FB len U L with
  | None => lkA = 0 /\ nL = 0%nat /\ LKb = []
  | Some Lb' => lkA = lk /\ nL = 12%nat /\ LKb = Lb'
  end.

Lemma cc_lock_same : forall FB U len lk L lkA nL LKb, cc_L L lk lkA nL LKb -> cm_lock FB len U L = L ->
  cc_lock FB U len lk L lkA nL LKb.
Proof.
  intros FB U len lk L lkA nL LKb H E. unfold cc_lock. rewrite E. unfold cc_L in H.
  destruct L as [Lb|]; [destruct H as (_ & _ & -> & -> & ->) | destruct H as (_ & -> & -> & ->)]; auto.
Qed.

Lemma cc_m1_k0 : forall F len U L O, dkind F len = 0 ->
  cm_ret F len U L = -1 /\ cm_out F len U L O = O /\ cm_lock F len U L = L.
Proof.
  intros F len U L O H. unfold cm_ret, cm_out, cm_lock, classify_model. cbv zeta. rewrite H.
  split; [|split]; reflexivity.
Qed.

Lemma cc_m1_eq : forall F len U L O, dkind F len <> 0 -> bytes_eqb (src F) U = true ->
  cm_ret F len U L = -1 /\ cm_out F len U L O = O /\ cm_lock F len U L = L.
Proof.
  intros F len U L O H E. unfold cm_ret, cm_out, cm_lock, classify_model. cbv zeta.
  rewrite (proj2 (Z.eqb_neq _ _) H), E. split; [|split]; reflexivity.
Qed.

Lemma cc_m1_sum : forall F len U L O, dkind F len <> 0 -> bytes_eqb (src F) U = false -> dkind F len <> 1 ->
  fsum F <> 0 -> cm_ret F len U L = -1 /\ cm_out F len U L O = O /\ cm_lock F len U L = L.
Proof.
  intros F len U L O H0 E H1 Sb. unfold cm_ret, cm_out, cm_lock, classify_model. cbv zeta.
  rewrite (proj2 (Z.eqb_neq _ _) H0), E, (proj2 (Z.eqb_neq _ _) H1), (proj2 (Z.eqb_neq _ _) Sb).
  split; [|split]; reflexivity.
Qed.

Lemma cc_m1_lock : forall F len U Lb O, dkind F len = 1 -> bytes_eqb (src F) U = false -> lv Lb <> 0 ->
  bytes_eqb (lm Lb) (src F) = false ->
  cm_ret F len U (Some Lb) = -1 /\ cm_out F len U (Some Lb) O = O /\ cm_lock F len U (Some Lb) = Some Lb.
Proof.
  intros F len U Lb O H E V B. unfold cm_ret, cm_out, cm_lock, classify_model. cbv beta iota zeta.
  rewrite H, E, (proj2 (Z.eqb_neq _ _) V), B. split; [|split]; reflexivity.
Qed.

Lemma cc_okJ : forall F len U L O lk lkA nL LKb, dkind F len <> 0 -> bytes_eqb (src F) U = false ->
  (dkind F len = 1 \/ fsum F = 0) ->
  (forall Lb, L = Some Lb -> dkind F len = 1 -> lv Lb <> 0 -> bytes_eqb (lm Lb) (src F) = true) ->
  match L with
  | None => lkA = 0 /\ nL = 0%nat /\ LKb = []
  | Some Lb => lkA = lk /\ nL = 12%nat /\ LKb = (if negb (dkind F len =? 1) && (lv Lb =? 0) then latch F Lb else Lb)
  end ->
  cm_ret F len U L = 0 /\ cm_out F len U L O = sight F len /\ cc_lock F U len lk L lkA nL LKb.
Proof.
  intros F len U L O lk lkA nL LKb H0 E HS HL HM. unfold cc_lock, cm_ret, cm_out, cm_lock, classify_model. cbv zeta.
  rewrite (proj2 (Z.eqb_neq _ _) H0), E.
  replace (negb (dkind F len =? 1) && negb (fsum F =? 0)) with false
    by (destruct HS as [HS|HS]; rewrite HS; [reflexivity | cbn [Z.eqb negb]; rewrite andb_false_r; reflexivity]).
  destruct L as [Lb|]; [| split; [reflexivity | split; [reflexivity | exact HM]]].
  cbv beta iota in HM |- *.
  destruct (Z.eqb_spec (dkind F len) 1) as [K1|K1].
  - destruct (Z.eqb_spec (lv Lb) 0) as [V|V].
    + cbn [negb andb]. split; [reflexivity | split; [reflexivity | exact HM]].
    + rewrite (HL Lb eq_refl K1 V). cbn [negb andb]. split; [reflexivity | split; [reflexivity | exact HM]].
  - cbn [negb andb]. split; [reflexivity | split; [reflexivity | exact HM]].
Qed.

Lemma cc_done : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m mk : word -> option byte) (lo lk len o : Z) (FB U OB : list byte) (L : option (list byte))
    (lkA : Z) (nL : nat) (LKb LKb' : list byte) (r : Z) (OUT : list byte) (ms' : machine_state),
  cc_L L lk lkA nL LKb ->
  munch [(bv_unsigned sp - 192, bv_unsigned sp); (lkA, lkA + Z.of_nat nL)] m mk -> wmono rsegs m mk ->
  cm_ret FB len U L = r -> cm_out FB len U L OB = OUT ->
  cc_lock FB U len lk L lkA nL LKb' -> rw_cells rsegs mk lkA [CB nL LKb'] ->
  (lkA + Z.of_nat nL <= bv_unsigned sp - 192 \/ bv_unsigned sp <= lkA) -> (lkA + Z.of_nat nL <= o \/ o + 24 <= lkA) ->
  cc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mk lo o r OUT ms' ->
  classify_core_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo lk len o FB U OB L ms'.
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mk lo lk len o FB U OB L lkA nL LKb LKb' r OUT ms'
    HLL MU1 WM1 Er Eo HLK RL D1 D2 P.
  destruct P as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU2 & WM2
    & MI & ST & RO).
  subst r OUT. unfold classify_core_post, CLASSIFY_CORE_K.
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [exact E|].
  split.
  { eapply munch_trans.
    - eapply munch_weaken; [|exact MU1]. intros x Hx. unfold cc_L in HLL.
      destruct L as [Lb|]; [destruct HLL as (_ & _ & -> & -> & _) | destruct HLL as (_ & -> & -> & _)];
        cbn [outside] in *; repeat split; try exact I; lia.
    - eapply munch_weaken; [|exact MU2]. intros x Hx.
      destruct L; cbn [outside] in *; repeat split; try exact I; lia. }
  split; [eapply wmono_trans; eassumption|].
  split; [exact MI|]. split; [exact ST|]. split; [exact RO|].
  unfold cc_lock in HLK. destruct (cm_lock FB len U L) as [Lb'|]; [|exact I].
  destruct HLK as (-> & -> & ->).
  eapply rw_cells_transport; [exact RL | exact MU2 | exact WM2 |].
  cbn [disjoint_from cells_size csize Nat.add]. repeat split; try exact I; lia.
Qed.

Lemma cc_lk1 : bcmp_contract ->
  forall (Q : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q lk lkA : Z) (nL : nat) (LKb SRC : list byte)
    (L : option (list byte)),
  s3 = Z_to_bv 64 q -> s4 = Z_to_bv 64 lk -> 0 <= q < 2 ^ 64 ->
  cc_L L lk lkA nL LKb -> rw_cells rsegs m lkA [CB nL LKb] ->
  bytes_at rsegs m q SRC -> length SRC = 6%nat -> mem_inv rsegs m ->
  (forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
     munch [] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
     (forall Lb, L = Some Lb -> lv Lb <> 0 -> bytes_eqb (lm Lb) SRC = true) ->
     evt rsegs Q (MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x154c4) fc None m' (seg_rom rsegs))) ->
  (forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte)
     (Lb : list byte),
     munch [] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
     L = Some Lb -> lv Lb <> 0 -> bytes_eqb (lm Lb) SRC = false ->
     evt rsegs Q (MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x1567c) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x15460) fc None m (seg_rom rsegs)).
Proof.
  intros BC Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    q lk lkA nL LKb SRC L Es3 Es4 Hq HLL RL BS LS MI KM KE.
  subst s3 s4. unfold BCMP in BC.
  destruct L as [Lb|]; unfold cc_L in HLL.
  2: { destruct HLL as (-> & -> & -> & ->).
       step. if_true.
       apply KM; [apply munch_refl | apply wmono_refl | exact MI | intros Lb E; discriminate E]. }
  destruct HLL as (Hlk & Hlk4 & -> & -> & ->).
  pose proof (rw_cells_bound rsegs m _ _ RL) as HB. cbn [cells_size csize Nat.add] in HB.
  change (Z.of_nat 12) with 12 in HB.
  destruct (cc_rwb _ _ _ _ RL) as [BL LL].
  assert (Ulk : bv_unsigned (Z_to_bv 64 lk) = lk) by (apply unsigned_lit; lia).
  assert (Ulk3 : bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 lk)) 3)) = 0).
  { rewrite Ulk. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2) with 4. rewrite Hlk4.
    reflexivity. }
  step. if_false.
  step. step. if_false.
  pose proof (cc_rd m lk Lb 8 4 BL ltac:(lia) ltac:(rewrite LL; cbn; lia)) as RD.
  step. rewrite disco_table.lw_val by (rewrite length_firstn, length_skipn, LL; reflexivity). clear RD.
  step.
  change (bytes_le_to_Z (firstn 4 (skipn _ Lb))) with (lv Lb).
  rewrite cc_lv0 by (apply cc_fu4; lia).
  destruct (Z.eqb_spec (lv Lb) 0) as [V0|V1]; cbv iota.
  { apply KM; [apply munch_refl | apply wmono_refl | exact MI |].
    intros Lb0 E V. injection E as <-. contradiction. }
  do 4 step.
  assert (LM : length (lm Lb) = 6%nat) by (unfold lm, fld; rewrite length_firstn, length_skipn; lia).
  destruct (disco_table.memcmp6 (lm Lb) SRC LM LS) as (v & Hv & Veq & Vr).
  eapply evt_cut.
  { eapply BC with (ls := lm Lb) (rs := SRC) (v := v).
    - rewrite Ulk. unfold lm. pose proof (bytes_sub m lk Lb 0 6 BL ltac:(lia)) as X.
      change (Z.of_nat 0) with 0 in X. rewrite Z.add_0_r in X. exact X.
    - rewrite unsigned_lit by lia. exact BS.
    - exact Hv.
    - exact MI. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU' & WM'
    & MI' & _ & _).
  subst ms'. fix_ret.
  step.
  rewrite disco_table.eqb_small by exact Vr.
  destruct (Z.eqb_spec v 0) as [W0|W1]; cbv iota.
  - apply KM; [exact MU' | exact WM' | exact MI' |].
    intros Lb0 E V. injection E as <-. apply cc_beqb. apply Veq. exact W0.
  - step.
    eapply KE; [exact MU' | exact WM' | exact MI' | reflexivity | exact V1 |].
    destruct (bytes_eqb (lm Lb) SRC) eqn:EB; [|reflexivity].
    exfalso. apply W1. apply Veq. apply cc_beqb. exact EB.
Qed.

Lemma cc_fsum : forall F, fsum F = blocksum (fld F 18 32).
Proof. reflexivity. Qed.

Lemma cc_lkn : reac_ctrl_checksum_verify_contract ->
  forall (Q : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (sp0 : word) (f len lk lkA : Z) (nL : nat)
    (LKb FB : list byte) (L : option (list byte)),
  s2 = Z_to_bv 64 f -> s3 = Z_to_bv 64 (bv_unsigned sp0 + -96) -> s4 = Z_to_bv 64 lk ->
  192 <= bv_unsigned sp0 ->
  0 < f -> f + 50 <= 2 ^ 64 -> bytes_at rsegs m f FB -> length FB = 50%nat ->
  cc_L L lk lkA nL LKb -> rw_cells rsegs m lkA [CB nL LKb] ->
  (lkA + Z.of_nat nL <= bv_unsigned sp0 - 192 \/ bv_unsigned sp0 <= lkA) ->
  rw_cells rsegs m (bv_unsigned sp0 + -100) (qcells FB len) -> mem_inv rsegs m ->
  (forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte)
     (LKb' : list byte),
     munch [(lkA, lkA + Z.of_nat nL)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
     fsum FB = 0 -> rw_cells rsegs m' lkA [CB nL LKb'] ->
     LKb' = match L with None => [] | Some Lb => if lv Lb =? 0 then latch FB Lb else Lb end ->
     evt rsegs Q (MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x154c4) fc None m' (seg_rom rsegs))) ->
  (forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
     fsum FB <> 0 ->
     evt rsegs Q (MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x1567c) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x1548c) fc None m (seg_rom rsegs)).
Proof.
  intros CHK Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    sp0 f len lk lkA nL LKb FB L Es2 Es3 Es4 S192 Hf0 Hfe HFB HFl HLL RL HLd HQ MI KM KE.
  subst s2 s3 s4. unfold REAC_CTRL_CHECKSUM_VERIFY in CHK.
  pose proof (bv_unsigned_in_range 64 sp0) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  unfold qcells in HQ.
  step. step.
  eapply evt_cut.
  { eapply CHK with (p := f) (bs := fld FB 18 32);
      [exact Hf0 | exact Hfe | reflexivity | unfold fld; rewrite length_firstn, length_skipn, HFl; reflexivity | ].
    exact (bytes_sub m f FB 18 32 HFB ltac:(lia)). }
  intros ms' (a1' & a2' & a3' & a4' & a5' & E). subst ms'. fix_ret.
  step.
  destruct (Z.eqb_spec (fsum FB) 0) as [S0|S1].
  2: { pose proof S1 as S1'. rewrite cc_fsum in S1'. rewrite (proj2 (Z.eqb_neq _ _) S1').
       if_true. apply KE. exact S1. }
  pose proof S0 as S0'. rewrite cc_fsum in S0'. rewrite S0'.
  if_false.
  destruct L as [Lb|]; unfold cc_L in HLL.
  2: { destruct HLL as (-> & -> & -> & ->).
       step. if_true.
       apply KM with (LKb' := []); [apply munch_refl | apply wmono_refl | exact MI | exact S0 | exact RL | reflexivity]. }
  destruct HLL as (Hlk & Hlk4 & -> & -> & ->).
  pose proof (rw_cells_bound rsegs m _ _ RL) as HB. cbn [cells_size csize Nat.add] in HB.
  change (Z.of_nat 12) with 12 in HB, HLd.
  destruct (cc_rwb _ _ _ _ RL) as [BL LL].
  assert (Ulk : bv_unsigned (Z_to_bv 64 lk) = lk) by (apply unsigned_lit; lia).
  assert (Ulk3 : bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 lk)) 3)) = 0).
  { rewrite Ulk. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2) with 4. rewrite Hlk4.
    reflexivity. }
  step. if_false.
  step. step. if_false.
  pose proof (cc_rd m lk Lb 8 4 BL ltac:(lia) ltac:(rewrite LL; cbn; lia)) as RD.
  step. rewrite disco_table.lw_val by (rewrite length_firstn, length_skipn, LL; reflexivity). clear RD.
  step.
  change (bytes_le_to_Z (firstn 4 (skipn _ Lb))) with (lv Lb).
  rewrite cc_lv0 by (apply cc_fu4; lia).
  destruct (Z.eqb_spec (lv Lb) 0) as [V0|V1]; cbn [negb].
  2: { apply KM with (LKb' := Lb); [apply munch_refl | apply wmono_refl | exact MI | exact S0 | exact RL |].
       cbv beta iota. try rewrite (proj2 (Z.eqb_neq _ _) V1). reflexivity. }
  clear BL.
  apply (rw_cells_split_CB rsegs m lk [] 12 Lb [] [4; 2; 2; 4]%nat) in RL; [|reflexivity].
  cbn [app mk_CB_cells] in RL.
  pose proof (munch_refl [(lk, lk + Z.of_nat 12)] m) as MUl. pose proof (wmono_refl rsegs m) as WMl.
  do 6 step.
  lazymatch goal with H : rw_cells rsegs ?mm lk _ |- _ => rename H into RL2 end.
  apply cc_merge with (Y := latch FB Lb) (n := 12%nat) in RL2.
  2: { unfold latch. cbn [cells_bytes cbytes]. rewrite app_nil_r, <- (src_lw FB HFl), !skipn_skipn.
       rewrite <- !app_assoc. reflexivity. }
  2: { reflexivity. }
  eapply KM; [exact MUl | exact WMl | eassumption | exact S0 | exact RL2 |].
  cbv beta iota. try rewrite (proj2 (Z.eqb_eq _ _) V0). reflexivity.
Qed.

Lemma cc_HM1 : forall F len L lk lkA nL LKb, cc_L L lk lkA nL LKb -> dkind F len = 1 ->
  match L with
  | None => lkA = 0 /\ nL = 0%nat /\ LKb = []
  | Some Lb => lkA = lk /\ nL = 12%nat /\ LKb = (if negb (dkind F len =? 1) && (lv Lb =? 0) then latch F Lb else Lb)
  end.
Proof.
  intros F len L lk lkA nL LKb H K. destruct L as [Lb|]; unfold cc_L in H.
  - destruct H as (_ & _ & -> & -> & ->). rewrite K. split; [reflexivity | split; reflexivity].
  - exact (proj2 H).
Qed.

Lemma cc_HMn : forall F len L lk lkA nL LKb LKb', cc_L L lk lkA nL LKb -> dkind F len <> 1 ->
  LKb' = match L with None => [] | Some Lb => if lv Lb =? 0 then latch F Lb else Lb end ->
  match L with
  | None => lkA = 0 /\ nL = 0%nat /\ LKb' = []
  | Some Lb => lkA = lk /\ nL = 12%nat /\ LKb' = (if negb (dkind F len =? 1) && (lv Lb =? 0) then latch F Lb else Lb)
  end.
Proof.
  intros F len L lk lkA nL LKb LKb' H K E. destruct L as [Lb|]; unfold cc_L in H; subst LKb'.
  - destruct H as (_ & _ & -> & -> & _). rewrite (proj2 (Z.eqb_neq _ _) K). cbn [negb andb].
    split; [reflexivity | split; reflexivity].
  - destruct H as (_ & -> & -> & _). split; [reflexivity | split; reflexivity].
Qed.

Lemma cc_fin_m1 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (sp0 vra v0 v1 v2 v3 v4 v5 v6 : word)
    (lo lk len o : Z) (FB U OB : list byte) (L : option (list byte)) (lkA : Z) (nL : nat) (LKb : list byte)
    (cw cq : list cell),
  cm_ret FB len U L = -1 /\ cm_out FB len U L OB = OB /\ cm_lock FB len U L = L ->
  sp = Z_to_bv 64 (bv_unsigned sp0 + -112) -> lo + 192 <= bv_unsigned sp0 ->
  cc_L L lk lkA nL LKb ->
  munch [(bv_unsigned sp0 - 192, bv_unsigned sp0); (lkA, lkA + Z.of_nat nL)] m0 m -> wmono rsegs m0 m ->
  rw_cells rsegs m lkA [CB nL LKb] ->
  (lkA + Z.of_nat nL <= bv_unsigned sp0 - 192 \/ bv_unsigned sp0 <= lkA) -> (lkA + Z.of_nat nL <= o \/ o + 24 <= lkA) ->
  stk rsegs m lo (bv_unsigned sp0 + -112) ->
  rw_cells rsegs m (bv_unsigned sp0 + -112) cw -> cells_size cw = 12%nat ->
  rw_cells rsegs m (bv_unsigned sp0 + -100) cq -> cells_size cq = 36%nat ->
  rw_cells rsegs m (bv_unsigned sp0 + -64) [C8 v6; C8 v5; C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 vra] ->
  rw_cells rsegs m o [CB 24 OB] -> mem_inv rsegs m ->
  evt rsegs (classify_core_post vra sp0 gp tp v0 v1 v2 v3 v4 v5 v6 s7 s8 s9 s10 s11 F fc m0 lo lk len o FB U OB L)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 (-1)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1567c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 m
    sp0 vra v0 v1 v2 v3 v4 v5 v6 lo lk len o FB U OB L lkA nL LKb cw cq (Er & Eo & El) Esp LO HLL MU WM RL D1 D2
    ST HW Hw HQ Hq SV HO HI.
  eapply evt_mono.
  - exact (cc_exit ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
             sp0 vra v0 v1 v2 v3 v4 v5 v6 lo o (-1) OB cw cq Esp LO ST HW Hw HQ Hq SV HO HI).
  - intros ms' P.
    exact (cc_done vra sp0 gp tp v0 v1 v2 v3 v4 v5 v6 s7 s8 s9 s10 s11 F fc m0 m lo lk len o FB U OB L lkA nL LKb LKb
             (-1) OB ms' HLL MU WM Er Eo (cc_lock_same FB U len lk L lkA nL LKb HLL El) RL D1 D2 P).
Qed.

Lemma cc_fin_ok : memset_contract -> reac_ports_parse_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (sp0 vra v0 v1 v2 v3 v4 v5 v6 : word)
    (lo lk len o f : Z) (FB U OB wj : list byte) (L : option (list byte)) (lkA : Z) (nL : nat) (LKb LKb' : list byte),
  cm_ret FB len U L = 0 /\ cm_out FB len U L OB = sight FB len /\ cc_lock FB U len lk L lkA nL LKb' ->
  sp = Z_to_bv 64 (bv_unsigned sp0 + -112) -> s0 = Z_to_bv 64 o -> s1 = Z_to_bv 64 len -> s2 = Z_to_bv 64 f ->
  s3 = Z_to_bv 64 (bv_unsigned sp0 + -96) -> dkind FB len <> 0 ->
  cc_L L lk lkA nL LKb ->
  munch [(bv_unsigned sp0 - 192, bv_unsigned sp0); (lkA, lkA + Z.of_nat nL)] m0 m -> wmono rsegs m0 m ->
  rw_cells rsegs m lkA [CB nL LKb'] ->
  (lkA + Z.of_nat nL <= bv_unsigned sp0 - 192 \/ bv_unsigned sp0 <= lkA) -> (lkA + Z.of_nat nL <= o \/ o + 24 <= lkA) ->
  bv_unsigned sp0 mod 16 = 0 -> lo + 192 <= bv_unsigned sp0 -> 0 <= len < 2 ^ 64 -> length FB = 50%nat ->
  0 < f -> bytes_at rsegs m f FB -> (f + 50 <= bv_unsigned sp0 - 192 \/ bv_unsigned sp0 <= f) ->
  0 < o -> o mod 4 = 0 ->
  (o + 24 <= bv_unsigned sp0 - 192 \/ bv_unsigned sp0 <= o) -> (o + 24 <= f \/ f + 50 <= o) ->
  stk rsegs m lo (bv_unsigned sp0 + -112) ->
  rw_cells rsegs m (bv_unsigned sp0 + -112) [CB 12 wj] ->
  rw_cells rsegs m (bv_unsigned sp0 + -100) (qcells FB len) ->
  rw_cells rsegs m (bv_unsigned sp0 + -64) [C8 v6; C8 v5; C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 vra] ->
  rw_cells rsegs m o [CB 24 OB] -> mem_inv rsegs m ->
  evt rsegs (classify_core_post vra sp0 gp tp v0 v1 v2 v3 v4 v5 v6 s7 s8 s9 s10 s11 F fc m0 lo lk len o FB U OB L)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x154c4) fc None m (seg_rom rsegs)).
Proof.
  intros MEMS PP ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
    m0 m sp0 vra v0 v1 v2 v3 v4 v5 v6 lo lk len o f FB U OB wj L lkA nL LKb LKb' (Er & Eo & HLK) Esp Es0 Es1 Es2 Es3
    Hk HLL MU WM RL D1 D2 S16 LO Hlen HFl Hf0 HFB HFd Ho0 Ho4 HOd HOF ST HW HQ SV HO HI.
  eapply evt_mono.
  - exact (cc_ms MEMS PP ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m sp0 vra v0 v1 v2 v3 v4 v5 v6 lo o len f FB wj OB Esp Es0 Es1 Es2 Es3 Hk S16 LO Hlen HFl Hf0 HFB
             HFd Ho0 Ho4 HOd HOF ST HW HQ SV HO HI).
  - intros ms' P.
    exact (cc_done vra sp0 gp tp v0 v1 v2 v3 v4 v5 v6 s7 s8 s9 s10 s11 F fc m0 m lo lk len o FB U OB L lkA nL LKb LKb'
             0 (sight FB len) ms' HLL MU WM Er Eo HLK RL D1 D2 P).
Qed.

Ltac cc_pro :=
  lazymatch goal with ST : stk rsegs _ _ _ |- _ => carve_frame 112%nat ST end;
  do 17 step;
  lazymatch goal with FR : rw_cells rsegs _ (bv_unsigned ?sp + -112) _ |- _ =>
    let F48 := fresh "F48" in
    destruct (cc_rw_split2 _ _ [CB 48 _] _ (bv_unsigned sp + -64) FR ltac:(cbn; lia)) as [F48 FS]; clear FR;
    apply (rw_cells_split_CB rsegs _ _ [] 48 _ [] [12; 36]%nat) in F48; [|reflexivity];
    cbn [app mk_CB_cells] in F48;
    destruct (cc_rw_split2 _ _ [CB 12 _] [CB 36 _] (bv_unsigned sp + -100) F48 ltac:(cbn; lia)) as [FW FQ0];
    clear F48;
    lazymatch goal with ST : stk rsegs _ ?lo (bv_unsigned sp + -112) |- _ =>
      destruct (stk_split rsegs _ lo (bv_unsigned sp + -192) (bv_unsigned sp + -112) ST ltac:(lia)) as [STl STh];
      clear ST
    end
  end.

Ltac cc_tr MU WM :=
  lazymatch type of MU with munch _ ?a ?b =>
    transport_after_call rsegs a b MU WM; clear MU WM;
    try (lazymatch goal with H : mem_inv rsegs a |- _ => clear H end)
  end.

Ltac cc_ap :=
  intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 cq MUc WMc MIc STc RQ Hcs HQK;
  cc_tr MUc WMc;
  lazymatch goal with STl : stk rsegs _ ?lo (bv_unsigned ?sp + -192) |- _ =>
    pose proof (stk_merge rsegs _ lo _ _ STl STc ltac:(lia)) as ST; clear STl STc
  end.

Ltac cc_m1 CM :=
  eapply cc_fin_m1;
  [ exact CM | reflexivity | lia | eassumption | eassumption | eassumption | eassumption | eassumption | eassumption
  | eassumption | eassumption | reflexivity | eassumption | first [ reflexivity | eassumption ] | eassumption
  | eassumption | eassumption ].

Theorem classify_core_holds : reac_ctrl_parse_contract -> bcmp_contract -> reac_ctrl_checksum_verify_contract ->
  memset_contract -> reac_ports_parse_contract -> classify_core_contract.
Proof.
  intros PARSE BC CHK MEMS PP. unfold classify_core_contract, classify_core_spec, CLASSIFY_CORE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo lk f len u o FB U OB L E0 E1 E2 E3 E4 PRE.
  unfold classify_core_pre, CLASSIFY_CORE_K, disj in PRE.
  destruct PRE as (Hsp16 & ST & HloS & Hlen & Hf & HFB & HF & HU6 & UB & Hud & Ho & Ho4 & O24 & Hod & Hou & HL & MI).
  subst a0 a1 a2 a3 a4.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof (rw_cells_bound _ _ _ _ O24) as HOB. cbn [cells_size csize Nat.add] in HOB.
  change (Z.of_nat 24) with 24 in HOB.
  pose proof (bytes_at_bound _ _ _ _ UB) as HUB. rewrite HU6 in HUB. change (Z.of_nat 6) with 6 in HUB.
  pose proof ST as (Hlo & _ & _).
  assert (LS : exists lkA nL LKb, cc_L L lk lkA nL LKb /\ rw_cells rsegs m lkA [CB nL LKb] /\ 0 <= lkA /\
     lkA + Z.of_nat nL <= 2^64 /\ (lkA + Z.of_nat nL <= bv_unsigned sp - 192 \/ bv_unsigned sp <= lkA) /\
     (lkA + Z.of_nat nL <= o \/ o + 24 <= lkA) /\ (50 <= len -> lkA + Z.of_nat nL <= f \/ f + 50 <= lkA)).
  { destruct L as [Lb|].
    - destruct HL as (Hlk & Hlk4 & RL & D1 & D2 & D3 & D4).
      pose proof (rw_cells_bound _ _ _ _ RL) as HRB. cbn [cells_size csize Nat.add] in HRB.
      change (Z.of_nat 12) with 12 in HRB.
      exists lk, 12%nat, Lb. split; [split; [exact Hlk | split; [exact Hlk4 | split; [reflexivity | split; reflexivity]]]|].
      split; [exact RL|]. change (Z.of_nat 12) with 12.
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. intros H50. specialize (D4 H50). lia.
    - exists 0, 0%nat, []. split; [split; [exact HL | split; [reflexivity | split; reflexivity]]|].
      split; [apply cc_rw_nil|]. change (Z.of_nat 0) with 0.
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. intros _. lia. }
  destruct LS as (lkA & nL & LKb & HLL & RL & HLa & HLb & HLf & HLo & HLfb). clear HL.
  pose proof (munch_refl [(bv_unsigned sp - 192, bv_unsigned sp); (lkA, lkA + Z.of_nat nL)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (ctrlparse_kind_range len FB) as KR. change (fst (ctrlparse len FB)) with (dkind FB len) in KR.
  assert (UK : bv_unsigned (Z_to_bv 64 (dkind FB len)) = dkind FB len) by (apply unsigned_lit; lia).
  destruct (Z_lt_le_dec len 50) as [Hs|Hb].
  -
    cc_pro.
    eapply (cc_parse PARSE) with (sp0 := sp) (f := f) (len := len) (FB := FB);
      [reflexivity | reflexivity | reflexivity | reflexivity | exact Hsp16 | lia | lia | lia | exact HFB
      | intros; lia | eassumption | eassumption | eassumption | ].
    cc_ap.
    assert (K0 : dkind FB len = 0) by (apply ctrlparse_none; intros [C' _]; lia).
    step. step. rewrite K0. if_true.
    cc_m1 (cc_m1_k0 FB len U L OB K0).
  - destruct (HF Hb) as (Hf0 & FBm & Hff & Hfo). specialize (HLfb Hb). clear HF.
    pose proof (bytes_at_bound _ _ _ _ FBm) as Hfb. rewrite HFB in Hfb. change (Z.of_nat 50) with 50 in Hfb.
    cc_pro.
    eapply (cc_parse PARSE) with (sp0 := sp) (f := f) (len := len) (FB := FB);
      [reflexivity | reflexivity | reflexivity | reflexivity | exact Hsp16 | lia | lia | lia | exact HFB
      | intros _; split; [lia | split; [eassumption | lia]] | eassumption | eassumption | eassumption | ].
    cc_ap.
    step. step.
    destruct (Z.eq_dec (dkind FB len) 0) as [K0|K0].
    { rewrite K0. if_true. cc_m1 (cc_m1_k0 FB len U L OB K0). }
    specialize (HQK K0). subst cq.
    if_false.

    do 5 step.
    pose proof (q_src _ _ _ _ HFB RQ) as QS.
    replace (bv_unsigned sp + -100 + 4) with (bv_unsigned sp + -96) in QS by lia.
    destruct (disco_table.memcmp6 (src FB) U (src_len FB HFB) HU6) as (v & Hv & Veq & Vr).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply BC with (ls := src FB) (rs := U) (v := v);
        [ rewrite unsigned_lit by lia; exact QS | rewrite unsigned_lit by lia; exact UB | exact Hv | eassumption ]
      | post_call rsegs mm ]
    end.
    step.
    rewrite disco_table.eqb_small by exact Vr.
    destruct (Z.eqb_spec v 0) as [W0|W1]; cbv iota.
    { assert (EQ : bytes_eqb (src FB) U = true) by (apply cc_beqb; apply Veq; exact W0).
      cc_m1 (cc_m1_eq FB len U L OB K0 EQ). }
    assert (HU : bytes_eqb (src FB) U = false).
    { destruct (bytes_eqb (src FB) U) eqn:B; [|reflexivity]. exfalso. apply W1. apply Veq. apply cc_beqb. exact B. }
    pose proof RQ as RQ'. unfold qcells in RQ'.
    step. clear RQ'.
    rewrite (sx32_small (dkind FB len)) by lia. step. step.
    destruct (Z.eq_dec (dkind FB len) 1) as [K1|K1].
    +
      if_false.
      eapply (cc_lk1 BC) with (q := bv_unsigned sp + -96) (lk := lk) (lkA := lkA) (nL := nL) (LKb := LKb)
        (SRC := src FB) (L := L);
        [reflexivity | reflexivity | lia | exact HLL | exact RL | exact QS | apply src_len; exact HFB | eassumption
        | | ].
      * intros ra' t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' m3 MU3 WM3 MI3 HLB.
        cc_tr MU3 WM3.
        eapply (cc_fin_ok MEMS PP) with (LKb := LKb) (LKb' := LKb);
          [ exact (cc_okJ FB len U L OB lk lkA nL LKb K0 HU (or_introl K1) (fun Lb E _ V => HLB Lb E V)
                     (cc_HM1 FB len L lk lkA nL LKb HLL K1))
          | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | exact K0 | exact HLL | eassumption
          | eassumption | eassumption | exact HLf | exact HLo | exact Hsp16 | lia | lia | exact HFB | exact Hf0
          | eassumption | lia | lia | exact Ho4 | lia | lia | eassumption | eassumption | eassumption | eassumption
          | eassumption | eassumption ].
      * intros ra' t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' m3 Lb MU3 WM3 MI3 EL V B.
        cc_tr MU3 WM3. subst L.
        cc_m1 (cc_m1_lock FB len U Lb OB K1 HU V B).
    +
      if_true.
      eapply (cc_lkn CHK) with (sp0 := sp) (f := f) (len := len) (lk := lk) (lkA := lkA) (nL := nL) (LKb := LKb)
        (FB := FB) (L := L);
        [reflexivity | reflexivity | reflexivity | lia | exact Hf0 | lia | eassumption | exact HFB | exact HLL
        | exact RL | exact HLf | eassumption | eassumption | | ].
      * intros ra' t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' m3 LKb' MU3 WM3 MI3 S0
          RL3 ELK.
        pose proof (stk_of_rw_cells rsegs m3 _ _ RL3) as SL3. cbn [cells_size csize] in SL3.
        rewrite Nat.add_0_r in SL3.
        pose proof (stk_patch _ m3 _ _ lkA (Z.of_nat nL) ST MU3 WM3 SL3) as ST3. clear SL3.
        cc_tr MU3 WM3.
        eapply (cc_fin_ok MEMS PP) with (LKb := LKb) (LKb' := LKb');
          [ exact (cc_okJ FB len U L OB lk lkA nL LKb' K0 HU (or_intror S0) (fun Lb _ K _ => False_ind _ (K1 K))
                     (cc_HMn FB len L lk lkA nL LKb LKb' HLL K1 ELK))
          | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | exact K0 | exact HLL | eassumption
          | eassumption | exact RL3 | exact HLf | exact HLo | exact Hsp16 | lia | lia | exact HFB | exact Hf0
          | eassumption | lia | lia | exact Ho4 | lia | lia | eassumption | eassumption | eassumption | eassumption
          | eassumption | eassumption ].
      * intros ra' t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' S1.
        cc_m1 (cc_m1_sum FB len U L OB K0 HU K1 S1).
Qed.
