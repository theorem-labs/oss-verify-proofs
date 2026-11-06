From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge FP Image.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model disco_json_reader_model disco_json_text.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_ser_defs slot_ser_tokb slot_ser_ws slot_ser_J0 slot_ser_J2.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import slot_inv slot_lib printf_facts_c json_scalar_c jtok_is_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import uslot_ser_ws uslot_ser uslot_ser_Pq uslot_ser_J1.
Import ListNotations.
Open Scope Z_scope.

Lemma uand7_zero : forall p, 0 <= p < 2 ^ 64 -> p mod 8 = 0 ->
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 p)) 7) = Z_to_bv 64 0.
Proof.
  intros p Hp H8. rewrite unsigned_lit by lia.
  change 7 with (Z.ones 3). rewrite (Z.land_ones p 3) by lia. change (2 ^ 3) with 8. rewrite H8. reflexivity.
Qed.

Lemma ucb_app2 : forall m A n1 n2 b1 b2, length b1 = n1 ->
  rw_cells rsegs m A [CB (n1 + n2) (b1 ++ b2)] ->
  rw_cells rsegs m A [CB n1 b1] /\ rw_cells rsegs m (A + Z.of_nat n1) [CB n2 b2].
Proof.
  intros m A n1 n2 b1 b2 L H.
  destruct (user_split m A (A + Z.of_nat n1) n1 n2 (n1 + n2) (b1 ++ b2) eq_refl eq_refl H) as [H1 H2].
  subst n1. rewrite firstn_app, firstn_all, Nat.sub_diag in H1. cbn [firstn] in H1. rewrite app_nil_r in H1.
  rewrite skipn_app, skipn_all, Nat.sub_diag in H2. cbn [skipn app] in H2. split; assumption.
Qed.

Lemma ucb_join : forall m A n1 n2 b1 b2,
  rw_cells rsegs m A [CB n1 b1] -> rw_cells rsegs m (A + Z.of_nat n1) [CB n2 b2] ->
  rw_cells rsegs m A [CB (n1 + n2) (b1 ++ b2)].
Proof. intros m A n1 n2 b1 b2 H1 H2. exact (user_join m A (A + Z.of_nat n1) n1 n2 (n1 + n2) b1 b2 eq_refl eq_refl H1 H2). Qed.

Lemma urw_addr : forall m A A' cs, rw_cells rsegs m A cs -> A = A' -> rw_cells rsegs m A' cs.
Proof. intros m A A' cs H E. subst A'. exact H. Qed.

Lemma uba_addr : forall m A A' bs, bytes_at rsegs m A bs -> A = A' -> bytes_at rsegs m A' bs.
Proof. intros m A A' bs H E. subst A'. exact H. Qed.

Lemma urd_all : forall m a bs, bytes_at rsegs m a bs -> ov_read_bytes rsegs m (wa a) (length bs) = Some bs.
Proof.
  intros m a bs H. pose proof (bytes_at_ov_read rsegs m a bs 0 (length bs) H ltac:(lia)) as R.
  cbn [Z.of_nat skipn] in R. rewrite Z.add_0_r, firstn_all in R. exact R.
Qed.

Lemma uzslot : forall m SA, rw_cells rsegs m SA [CB 24 (repeat (Z_to_bv 8 0) 24)] ->
  rw_cells rsegs m SA [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
Proof.
  intros m SA [[_ B] W]. split; [split|].
  - cbn [cells_wf cell_wf]. tauto.
  - cbn [cells_bytes cbytes] in B |- *.
    replace (le8 (Z_to_bv 64 0) ++ le8 (Z_to_bv 64 0) ++ le8 (Z_to_bv 64 0) ++ [])
      with (repeat (Z_to_bv 8 0) 24 ++ []) by (vm_compute; reflexivity).
    exact B.
  - exact W.
Qed.

Lemma uzslot_rd : forall m SA, rw_cells rsegs m SA [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  ov_read_bytes rsegs m (wa (SA + 16)) 4 = Some (le4 (Z_to_bv 64 0)).
Proof.
  intros m SA [[_ B] _].
  rewrite (bytes_at_read rsegs m SA _ 16 4 B)
    by first [lia | (cbn [cells_bytes cbytes]; rewrite !length_app, !length_le8; cbn [length]; lia)].
  vm_compute. reflexivity.
Qed.

Lemma utok_cells : forall m V w0 w1 w2, bytes_at rsegs m V (le8 w0 ++ le8 w1 ++ le4 w2) -> wr_at rsegs m V 20 ->
  rw_cells rsegs m V [C8 w0; C8 w1; C4 w2].
Proof.
  intros m V w0 w1 w2 B W. split; [split|].
  - cbn [cells_wf cell_wf]. tauto.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B.
  - exact W.
Qed.

Lemma ucells_cb3 : forall m V w0 w1 w2, rw_cells rsegs m V [C8 w0; C8 w1; C4 w2] ->
  rw_cells rsegs m V [CB 20 (le8 w0 ++ le8 w1 ++ le4 w2)].
Proof.
  intros m V w0 w1 w2 [[_ B] W]. apply user_cb. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
  split; [rewrite !length_app, !length_le8, length_le4; reflexivity|]. split; [exact B|exact W].
Qed.

Lemma ucells_c83 : forall m V w0 w1 w2, rw_cells rsegs m V [C8 w0; C8 w1; C8 w2] ->
  rw_cells rsegs m V [CB 24 (le8 w0 ++ le8 w1 ++ le8 w2)].
Proof.
  intros m V w0 w1 w2 [[_ B] W]. apply user_cb. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
  split; [rewrite !length_app, !length_le8; reflexivity|]. split; [exact B|exact W].
Qed.

Lemma uws12w : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (b i : Z) (B : list Z),
  s1 = Z_to_bv 64 (nt b) -> s2 = Z_to_bv 64 WS_MASK -> s3 = Z_to_bv 64 b -> s4 = Z_to_bv 64 (jlen B) ->
  s10 = Z_to_bv 64 32 -> a0 = Z_to_bv 64 i ->
  0 <= i < jlen B -> 0 < b -> b + jlen B + 1 < 2 ^ 63 ->
  Forall (fun c => 0 <= c < 256) B -> bytes_at rsegs m b (pf_bytes (B ++ [0])) ->
  evt rsegs
    (fun ms' => exists a0' : word,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' (Z_to_bv 64 (json_ws B (i + 1))) a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x139bc) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1398c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m b i B
    E1 E2 E3 E4 E10 Ea Hi Hb HbB FB BB.
  subst s1 s2 s3 s4 s10 a0.
  step.
  eapply uws_L12 with (b := b) (i := i + 1) (B := B);
    first [reflexivity | (f_equal; lia) | (rewrite unsigned_lit by lia; f_equal; lia) | lia | assumption].
Qed.

Lemma uws14w : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (b i : Z) (B : list Z),
  s1 = Z_to_bv 64 (nt b) -> s2 = Z_to_bv 64 WS_MASK -> s3 = Z_to_bv 64 b -> s4 = Z_to_bv 64 (jlen B) ->
  s10 = Z_to_bv 64 32 -> s6 = Z_to_bv 64 i ->
  0 <= i < jlen B -> 0 < b -> b + jlen B + 1 < 2 ^ 63 ->
  Forall (fun c => 0 <= c < 256) B -> bytes_at rsegs m b (pf_bytes (B ++ [0])) ->
  evt rsegs
    (fun ms' => exists a0' : word,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' (Z_to_bv 64 (json_ws B (i + 1))) a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x13b44) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13b14) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m b i B
    E1 E2 E3 E4 E10 E6 Hi Hb HbB FB BB.
  subst s1 s2 s3 s4 s10 s6.
  step.
  eapply uws_L14 with (b := b) (i := i + 1) (B := B);
    first [reflexivity | (f_equal; lia) | (rewrite unsigned_lit by lia; f_equal; lia) | lia | assumption].
Qed.

Lemma uslot_put : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (SA V : Z) (w0 w1 : word) (bs2 : list byte),
  a0 = Z_to_bv 64 SA -> s8 = Z_to_bv 64 (V + 16) -> length bs2 = 8%nat ->
  0 <= SA -> SA + 24 < 2 ^ 63 -> 0 <= V -> V + 24 < 2 ^ 63 ->
  rw_cells rsegs m SA [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  ov_read_bytes rsegs m (wa V) 8 = Some (le8 w0) ->
  ov_read_bytes rsegs m (wa (V + 8)) 8 = Some (le8 w1) ->
  ov_read_bytes rsegs m (wa (V + 16)) 8 = Some bs2 ->
  mem_inv rsegs m ->
  evt rsegs
    (fun ms' => exists (a1' a2' a3' : word) (m' : word -> option byte),
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x13b00) fc None m' (seg_rom rsegs) /\
       munch [(SA, SA + 24)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
       rw_cells rsegs m' SA [CB 24 (le8 w0 ++ le8 w1 ++ bs2)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13ae0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SA V w0 w1
    bs2 Ea0 Es8 L2 H1 H2 H3 H4 C R0 R1 R2 MI.
  subst a0 s8.
  pose proof (uzslot_rd m SA C) as R16.
  pose proof (munch_refl [(SA, SA + 24)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  step. step. if_vm.
  step. step. step.
  step. step. step.
  apply evt_done. do 4 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
  apply ucells_c83 in C.
  first [rewrite (le8_inv bs2 L2) in C | rewrite (le8_inv2 bs2 L2) in C]. exact C.
Qed.

Ltac ujs_side := unfold JSON_SCALAR_K in *;
  first [ reflexivity | assumption | (f_equal; lia) | (rewrite ?unsigned_lit by lia; f_equal; lia) | lia ].

Lemma ukey_head : json_scalar_contract -> jtok_is_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (lo X b cur i j ks kl r : Z) (B : list Z) (o o' : jobj) (f : nat) (vpk vpad jv : list byte),
  sp = Z_to_bv 64 X -> s1 = Z_to_bv 64 (nt b) -> s2 = Z_to_bv 64 WS_MASK -> s3 = Z_to_bv 64 b ->
  s4 = Z_to_bv 64 (jlen B) -> s5 = Z_to_bv 64 cur -> s7 = Z_to_bv 64 (cur + 24) -> s0 = Z_to_bv 64 (cur + 48) ->
  s8 = Z_to_bv 64 (X + 2368) -> s10 = Z_to_bv 64 32 -> s11 = Z_to_bv 64 0 -> a0 = Z_to_bv 64 j ->
  X mod 16 = 0 -> cur mod 8 = 0 ->
  0 <= i -> jscalar B i = Some (j, 1, ks, kl) -> json_pairs B i o (S f) = Some (r, o') ->
  length o = 6%nat -> Forall (tok_inb B) o -> length vpk = 4%nat -> length vpad = 4%nat -> length jv = 20%nat ->
  0 < b -> b + jlen B + 1 <= lo -> Forall (fun c => 0 <= c < 256) B -> bytes_at rsegs m b (pf_bytes (B ++ [0])) ->
  rw_cells rsegs m (X + 1024) [CB 20 (le8 (Z_to_bv 64 (b + ks)) ++ le8 (Z_to_bv 64 kl) ++ le4 (Z_to_bv 64 1))] ->
  rw_cells rsegs m (X + 1044) [CB 4 vpk] ->
  rw_cells rsegs m (X + 248) [C8 (Z_to_bv 64 (cur + 72))] -> rw_cells rsegs m (X + 232) [C8 (Z_to_bv 64 (cur + 96))] ->
  rw_cells rsegs m (X + 208) [C8 (Z_to_bv 64 (cur + 120))] ->
  rw_cells rsegs m cur [CB 144 (obj_bytes b vpad o)] ->
  rw_cells rsegs m (X + 2352) [CB 20 jv] -> rw_cells rsegs m (X + 2372) [CB 4 vpad] ->
  X + 1056 <= cur -> cur + 144 <= X + 2352 ->
  bytes_at rsegs m JSON_SCALAR_L js_table -> mem_inv rsegs m -> stk rsegs m lo X -> lo + 112 <= X -> 0x524f8 <= lo ->
  X + 2624 < 2 ^ 63 ->
  evt rsegs
    (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                       (m' : word -> option byte) (i3 : Z) (o1 : jobj) (jv' : list byte),
       ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                     s2 s3 s4 s5 (Z_to_bv 64 i3) s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x13b00) fc None m' (seg_rom rsegs) /\
       munch [(lo, X); (cur, cur + 144); (X + 2352, X + 2372)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
       stk rsegs m' lo X /\
       rw_cells rsegs m' cur [CB 144 (obj_bytes b vpad o1)] /\ rw_cells rsegs m' (X + 2352) [CB 20 jv'] /\
       0 <= i3 <= jlen B /\ length o1 = 6%nat /\ Forall (tok_inb B) o1 /\
       ((at_byte B i3 44 = true /\ json_pairs B (json_ws B (i3 + 1)) o1 f = Some (r, o')) \/
        (at_byte B i3 44 = false /\ at_byte B i3 125 = true /\ r = i3 + 1 /\ o' = o1)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1394c) fc None m (seg_rom rsegs)).
Proof.
  intros JS JT ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo X b cur i j ks kl r B o o' f vpk vpad jv
    Esp Es1 Es2 Es3 Es4 Es5 Es7 Es0 Es8 Es10 Es11 Ea0 HX16 Hc8 Hi JSk JP Lo Io Lk Lv Ljv Hb Hbl FB BB CK CV
    C248 C232 C208 CO CJ CP Hc1 Hc2 JTB MI ST HK HI HX.
  assert (LBB : Z.of_nat (length (pf_bytes (B ++ [0]))) = jlen B + 1)
    by (rewrite ulength_pf_bytes, length_app; unfold jlen; cbn [length]; lia).
  assert (HV8 : (X + 2352) mod 8 = 0) by (clear - HX16; Z.div_mod_to_equations; lia).
  pose proof (jscalar_bnd B i j 1 ks kl JSk Hi) as (Hks & Hkl & Hkb & Hj0).
  cbn [json_pairs] in JP. rewrite JSk in JP. cbv iota zeta in JP. rewrite Z.eqb_refl in JP. cbn [negb] in JP.
  cbv iota in JP.
  set (i1 := json_ws B j) in *.
  destruct (at_byte B i1 58) eqn:A1; cbn [negb] in JP; cbv iota in JP; [|discriminate JP].
  set (i2 := json_ws B (i1 + 1)) in *.
  destruct (jscalar B i2) as [[[[j2 vk] vs] vl]|] eqn:JS2; cbv iota in JP; [|discriminate JP].
  set (i3 := json_ws B j2) in *.
  pose proof (ws_ge B j Hj0) as G1. fold i1 in G1.
  destruct (at_byte_true B i1 58 A1) as [L1 C1].
  pose proof (ws_ge B (i1 + 1) ltac:(lia)) as G2. fold i2 in G2.
  pose proof (ws_le B (i1 + 1) ltac:(lia)) as G2'. fold i2 in G2'.
  pose proof (js_rng B i2 j2 vk vs vl JS2) as [L2 G3].
  pose proof (jscalar_bnd B i2 j2 vk vs vl JS2 ltac:(lia)) as (Hvs & Hvl & Hvb & _).
  pose proof (jscalar_kind B i2 j2 vk vs vl JS2) as Hvk.
  pose proof (ws_ge B j2 ltac:(lia)) as G4. fold i3 in G4.
  pose proof (ws_le B j2 ltac:(lia)) as G4'. fold i3 in G4'.
  pose proof CJ as CJw. apply user_cb in CJw as (_ & _ & WV).
  subst sp s1 s2 s3 s4 s5 s7 s0 s8 s10 s11 a0.
  pose proof (munch_refl [(lo, X); (cur, cur + 144); (X + 2352, X + 2372)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  eapply evt_cut.
  { eapply (uws_L11 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m b j B);
      first [reflexivity | (f_equal; lia) | lia | assumption]. }
  intros ms' [a1x E]. subst ms'. fold i1.
  step. rewrite ltu_lit by lia. replace (i1 <? jlen B) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb]. cbv iota.
  pose proof (uws_rd m b B i1 BB ltac:(lia)) as RD1. pose proof (ws_byte B i1 FB) as HC1.
  step. step. rewrite ws_zxb by lia. step. step. rewrite eqb_lit by lia. rewrite C1, Z.eqb_refl. cbn [negb]. cbv iota.
  eapply evt_cut.
  { eapply uws12w with (b := b) (i := i1) (B := B); first [reflexivity | lia | assumption]. }
  intros ms' [a0x E]. subst ms'. fold i2.
  step. step. step. step. step.
  eapply (ujs_call JS) with (lo := lo) (X := X) (b := b) (i := i2) (V := X + 2352) (B := B) (j := j2) (k := vk)
    (s := vs) (l := vl); [ujs_side .. | ].
  intros m1 ? ? ? ? ? ? ? ? ? ? ? ? ? ? MU1 WM1 MI1 ST1 BV.
  rewrite (ret_pc_even 0x139d0) by (first [lia | reflexivity]).
  unfold JSON_SCALAR_K in MU1.
  transport_after_call rsegs m m1 MU1 WM1. clear MU1 WM1 MI.
  assert (CJ1 : rw_cells rsegs m1 (X + 2352)
                  [CB 20 (le8 (Z_to_bv 64 (b + vs)) ++ le8 (Z_to_bv 64 vl) ++ le4 (Z_to_bv 64 vk))]).
  { apply user_cb. split; [rewrite !length_app, !length_le8, length_le4; reflexivity|]. split; [exact BV | exact WV]. }
  clear BV.
  step. rewrite eqb_lit by lia. replace (j2 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb]. cbv iota.
  eapply evt_cut.
  { eapply uws_L13 with (b := b) (i := j2) (B := B); first [reflexivity | lia | assumption]. }
  intros ms' [a0y E]. subst ms'. fold i3.
  eapply evt_cut.
  { eapply (uslot_jt JT) with (lo := lo) (X := X) (b := b) (cur := cur) (ks := ks) (kl := kl) (B := B) (vpk := vpk);
      first [reflexivity | lia | assumption]. }
  intros ms' (ra2 & t02 & t12 & t22 & a02 & a12 & a22 & a32 & a42 & a52 & a62 & a72 & t32 & t42 & t52 & t62 & m2 &
              MU2 & WM2 & MI2 & ST2 & E).
  subst ms'. transport_after_call rsegs m1 m2 MU2 WM2. clear MU2 WM2 MI1.
  destruct (slot_of B (1, ks, kl)) as [k|] eqn:SO; cbv iota in JP |- *.
  - pose proof (slot_of_lt B (1, ks, kl) k SO) as Hk6.
    destruct (tv_kind (nth k o tok_none) =? 0) eqn:K0; cbv iota in JP; [|discriminate JP].
    apply Z.eqb_eq in K0.
    assert (Hko : (k < length o)%nat) by lia.
    assert (MD : (at_byte B i3 44 = true /\ json_pairs B (json_ws B (i3 + 1)) (set_nth k o (vk, vs, vl)) f = Some (r, o')) \/
                 (at_byte B i3 44 = false /\ at_byte B i3 125 = true /\ r = i3 + 1 /\ o' = set_nth k o (vk, vs, vl))).
    { destruct (at_byte B i3 44) eqn:A3; cbv iota in JP; [left; split; [reflexivity|exact JP]|].
      destruct (at_byte B i3 125) eqn:A4; cbv iota in JP; [|discriminate JP].
      injection JP as Er Eo. right. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. symmetry. exact Eo. }
    clear JP.
    rewrite (obj_split b vpad o k Hko) in CO.
    pose proof (obj_pre_len b vpad o k Lv ltac:(lia)) as LA.
    rewrite (slot24_zero b vpad _ K0) in CO.
    replace 144%nat with (24 * k + (24 + (120 - 24 * k)))%nat in CO by lia.
    apply ucb_app2 in CO as [CA CO']; [|exact LA].
    apply ucb_app2 in CO' as [CZ CPo]; [|apply repeat_length].
    apply uzslot in CZ.
    pose proof (urw_addr _ _ (cur + 24 * Z.of_nat k) _ CZ ltac:(lia)) as CZ'. clear CZ.
    pose proof (user_cb_bytes _ _ _ _ CJ1) as BJ. pose proof (user_cb_bytes _ _ _ _ CP) as BP.
    apply bytes_at_app in BJ as [B0 BJ']. apply bytes_at_app in BJ' as [B1 B2].
    assert (R0 : ov_read_bytes rsegs m2 (wa (X + 2352)) 8 = Some (le8 (Z_to_bv 64 (b + vs)))).
    { pose proof (urd_all _ _ _ B0) as R. rewrite length_le8 in R. exact R. }
    assert (R1 : ov_read_bytes rsegs m2 (wa (X + 2352 + 8)) 8 = Some (le8 (Z_to_bv 64 vl))).
    { pose proof (urd_all _ _ _ (uba_addr _ _ (X + 2352 + 8) _ B1 ltac:(rewrite length_le8; lia))) as R.
      rewrite length_le8 in R. exact R. }
    assert (R2 : ov_read_bytes rsegs m2 (wa (X + 2352 + 16)) 8 = Some (le4 (Z_to_bv 64 vk) ++ vpad)).
    { assert (B2' : bytes_at rsegs m2 (X + 2352 + 16) (le4 (Z_to_bv 64 vk) ++ vpad)).
      { apply bytes_at_app. split.
        - apply (uba_addr _ _ _ _ B2). rewrite !length_le8. lia.
        - apply (uba_addr _ _ _ _ BP). rewrite length_le4. lia. }
      pose proof (urd_all _ _ _ B2') as R. rewrite length_app, length_le4, Lv in R. exact R. }
    clear B0 B1 B2 BP.
    eapply evt_cut.
    { eapply uslot_put with (SA := cur + 24 * Z.of_nat k) (V := X + 2352) (w0 := Z_to_bv 64 (b + vs))
        (w1 := Z_to_bv 64 vl) (bs2 := le4 (Z_to_bv 64 vk) ++ vpad);
        first [reflexivity | (f_equal; lia) | (rewrite length_app, length_le4, Lv; reflexivity) | lia | assumption]. }
    intros ms' (a1z & a2z & a3z & m3 & E & MU3 & WM3 & MI3 & CS3). subst ms'.
    transport_after_call rsegs m2 m3 MU3 WM3. clear MU3 WM3 MI2.
    pose proof (urw_addr _ _ (cur + Z.of_nat (24 * k)) _ CS3 ltac:(lia)) as CS4.
    pose proof (ucb_join _ _ _ _ _ _ CS4 CPo) as CJ2.
    pose proof (ucb_join _ _ _ _ _ _ CA CJ2) as CO2.
    assert (CO3 : rw_cells rsegs m3 cur [CB 144 (obj_bytes b vpad (set_nth k o (vk, vs, vl)))]).
    { rewrite (obj_set b vpad o k (vk, vs, vl) Hko). rewrite (slot24_val b vpad vk vs vl ltac:(lia)).
      replace 144%nat with (24 * k + (24 + (120 - 24 * k)))%nat by lia. exact CO2. }
    apply evt_done. do 18 eexists.
    exists (set_nth k o (vk, vs, vl)), (le8 (Z_to_bv 64 (b + vs)) ++ le8 (Z_to_bv 64 vl) ++ le4 (Z_to_bv 64 vk)).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI3|]. split; [exact ST2|].
    split; [exact CO3|]. split; [exact CJ1|]. split; [lia|].
    split; [rewrite set_nth_length; exact Lo|].
    split; [apply set_nth_forall; [exact Io | right; cbn [fst snd]; lia]|].
    exact MD.
  - assert (MD : (at_byte B i3 44 = true /\ json_pairs B (json_ws B (i3 + 1)) o f = Some (r, o')) \/
                 (at_byte B i3 44 = false /\ at_byte B i3 125 = true /\ r = i3 + 1 /\ o' = o)).
    { destruct (at_byte B i3 44) eqn:A3; cbv iota in JP; [left; split; [reflexivity|exact JP]|].
      destruct (at_byte B i3 125) eqn:A4; cbv iota in JP; [|discriminate JP].
      injection JP as Er Eo. right. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. symmetry. exact Eo. }
    clear JP.
    apply evt_done. do 18 eexists.
    exists o, (le8 (Z_to_bv 64 (b + vs)) ++ le8 (Z_to_bv 64 vl) ++ le4 (Z_to_bv 64 vk)).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI2|]. split; [exact ST2|].
    split; [exact CO|]. split; [exact CJ1|]. split; [lia|]. split; [exact Lo|]. split; [exact Io|].
    exact MD.
Qed.
