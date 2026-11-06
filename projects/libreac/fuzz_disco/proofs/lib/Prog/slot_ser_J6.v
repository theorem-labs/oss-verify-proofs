From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge FP Image.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv slot_lib printf_facts_c slot_ser_defs.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import json_scalar_c jtok_is_c tj_lemmas.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model disco_json_reader_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_ser_tokb slot_ser_ws slot_ser_J0 slot_ser slot_ser_J2.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_ser_J4 slot_ser_J5.
Import ListNotations.
Open Scope Z_scope.

Lemma json_pairs_gt : forall B f i cur r c, json_pairs B i cur f = Some (r, c) -> 0 <= i -> i < r.
Proof.
  intros B f. induction f as [|f IH]; intros i cur r c H Hi; cbn [json_pairs] in H; cbv zeta in H.
  - discriminate.
  - destruct (jscalar B i) as [[[[j kk] ks] kl]|] eqn:E1; cbv beta iota in H; [|discriminate].
    pose proof (js_rng B i j kk ks kl E1) as [_ Hj].
    destruct (negb (kk =? 1)) eqn:E2; cbv beta iota in H; [discriminate|].
    destruct (negb (at_byte B (json_ws B j) 58)) eqn:E3; cbv beta iota in H; [discriminate|].
    pose proof (json_ws_ge B j) as W1. pose proof (json_ws_ge B (json_ws B j + 1)) as W2.
    destruct (jscalar B (json_ws B (json_ws B j + 1))) as [[[[j2 vk] vs] vl]|] eqn:E4;
      cbv beta iota in H; [|discriminate].
    pose proof (js_rng B _ j2 vk vs vl E4) as [_ Hj2].
    pose proof (json_ws_ge B j2) as W3. pose proof (json_ws_ge B (json_ws B j2 + 1)) as W4.
    destruct (slot_of B (kk, ks, kl)) as [k|] eqn:E5; cbv beta iota in H.
    + destruct (tv_kind (nth k cur tok_none) =? 0) eqn:E6; cbv beta iota in H; [|discriminate].
      destruct (at_byte B (json_ws B j2) 44) eqn:E7; cbv beta iota in H.
      * pose proof (IH _ _ _ _ H ltac:(lia)). lia.
      * destruct (at_byte B (json_ws B j2) 125) eqn:E8; cbv beta iota in H; [|discriminate].
        injection H; intros; subst. lia.
    + destruct (at_byte B (json_ws B j2) 44) eqn:E7; cbv beta iota in H.
      * pose proof (IH _ _ _ _ H ltac:(lia)). lia.
      * destruct (at_byte B (json_ws B j2) 125) eqn:E8; cbv beta iota in H; [|discriminate].
        injection H; intros; subst. lia.
Qed.

Lemma json_objs_lt : forall B f i c max acc count os, json_objs B i c max acc f = Some (count, os) -> c < count.
Proof.
  intros B f. induction f as [|f IH]; intros i c max acc count os H; cbn [json_objs] in H; cbv zeta in H.
  - discriminate.
  - destruct (negb (at_byte B i 123)) eqn:E1; cbv beta iota in H; [discriminate|].
    match type of H with
    | context [match ?x with _ => _ end] => destruct x as [[i2 cur]|] eqn:E2
    end; cbv beta iota in H; [|discriminate].
    destruct (at_byte B (json_ws B i2) 44) eqn:E3; cbv beta iota in H.
    + pose proof (IH _ _ _ _ _ _ H). lia.
    + destruct (at_byte B (json_ws B i2) 93) eqn:E4; cbv beta iota in H; [|discriminate].
      destruct (json_ws B (json_ws B i2 + 1) =? jlen B) eqn:E5; cbv beta iota in H; [|discriminate].
      injection H; intros; subst. lia.
Qed.

Lemma objs_bytes_snoc : forall b vpad acc o, objs_bytes b vpad (acc ++ [o]) = objs_bytes b vpad acc ++ obj_bytes b vpad o.
Proof.
  intros b vpad acc o. unfold objs_bytes. rewrite map_app, concat_app. cbn [map concat]. rewrite app_nil_r. reflexivity.
Qed.

Lemma obj_loop : json_scalar_contract -> jtok_is_contract ->
  forall (f : nat) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (lo X b c i count now : Z) (B : list Z) (acc os : list jobj) (jk vpk jv vpad j216 j192 jr : list byte),
  sp = Z_to_bv 64 X -> s0 = Z_to_bv 64 32 -> s1 = Z_to_bv 64 c -> s2 = Z_to_bv 64 WS_MASK -> s3 = Z_to_bv 64 b ->
  s4 = Z_to_bv 64 (jlen B) -> s5 = Z_to_bv 64 (X + 1024 + 144 * c) -> s7 = Z_to_bv 64 (- jlen B) ->
  s8 = Z_to_bv 64 (X + 2336) -> s9 = Z_to_bv 64 1 -> s10 = Z_to_bv 64 i -> s11 = Z_to_bv 64 now ->
  0 <= c -> 0 <= i -> json_objs B i c 9 acc f = Some (count, os) -> count <= 8 ->
  length vpk = 4%nat -> length vpad = 4%nat -> length jv = 20%nat ->
  0 < b -> b + jlen B + 1 <= lo -> Forall (fun c => 0 <= c < 256) B -> bytes_at rsegs m b (pf_bytes (B ++ [0])) ->
  rw_cells rsegs m (X + 992) [CB 20 jk] -> rw_cells rsegs m (X + 1012) [CB 4 vpk] ->
  rw_cells rsegs m (X + 216) [CB 8 j216] -> rw_cells rsegs m (X + 192) [CB 8 j192] ->
  rw_cells rsegs m (X + 224) [C8 (Z_to_bv 64 (b + 1))] ->
  rw_cells rsegs m (X + 1024) [CB (Z.to_nat (144 * c)) (objs_bytes b vpad acc)] ->
  rw_cells rsegs m (X + 1024 + 144 * c) [CB 144 (repeat (Z_to_bv 8 0) 144)] ->
  rw_cells rsegs m (X + 1168 + 144 * c) [CB (Z.to_nat (1152 - 144 * c)) jr] ->
  rw_cells rsegs m (X + 2320) [CB 20 jv] -> rw_cells rsegs m (X + 2340) [CB 4 vpad] ->
  rw_cells rsegs m (X + 200) [C8 (Z_to_bv 64 now)] ->
  bytes_at rsegs m JSON_SCALAR_L js_table -> mem_inv rsegs m -> stk rsegs m lo X -> lo + 112 <= X -> 0x51d38 <= lo ->
  X + 2592 < 2 ^ 63 ->
  evt rsegs
    (fun ms' => exists (ra' t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s5' s9' s10' t3' t4' t5' t6' : word)
                       (m' : word -> option byte) (jk' jv' j216' j192' jo' : list byte),
       ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1' a0' a1' a2' a3' a4' a5' a6' a7'
                     s2 s3 s4 s5' (Z_to_bv 64 count) s7 s8 s9' s10' s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x140bc) fc None m' (seg_rom rsegs) /\
       munch [(lo, X); (X + 192, X + 200); (X + 216, X + 224); (X + 992, X + 1012); (X + 1024, X + 2320);
              (X + 2320, X + 2340)] m m' /\
       wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo X /\
       rw_cells rsegs m' (X + 1024) [CB (Z.to_nat (144 * count)) (objs_bytes b vpad os)] /\
       rw_cells rsegs m' (X + 1024 + 144 * count) [CB (Z.to_nat (1296 - 144 * count)) jo'] /\
       rw_cells rsegs m' (X + 992) [CB 20 jk'] /\ rw_cells rsegs m' (X + 2320) [CB 20 jv'] /\
       rw_cells rsegs m' (X + 216) [CB 8 j216'] /\ rw_cells rsegs m' (X + 192) [CB 8 j192'])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13954) fc None m (seg_rom rsegs)).
Proof.
  intros JS JT f. induction f as [|f IH];
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
      lo X b c i count now B acc os jk vpk jv vpad j216 j192 jr
      Esp Es0 Es1 Es2 Es3 Es4 Es5 Es7 Es8 Es9 Es10 Es11 Hc Hi JO Hcnt Lk Lv Ljv Hb Hbl FB BB CK CV C216 C192 C224
      CA CO CR CJ CP C200 JTB MI ST HK HI HX; [discriminate JO|].
  assert (HJL : JSON_SCALAR_L = 0x1fe28) by reflexivity.
  assert (LJS : Z.of_nat (length js_table) = 24) by reflexivity.
  assert (LBB : Z.of_nat (length (pf_bytes (B ++ [0]))) = jlen B + 1)
    by (rewrite length_pf_bytes, length_app; unfold jlen; cbn [length]; lia).
  pose proof (json_objs_lt B (S f) i c 9 acc count os JO) as Hlt.
  assert (LA : Z.of_nat (Z.to_nat (144 * c)) = 144 * c) by lia.
  assert (LR : Z.of_nat (Z.to_nat (1152 - 144 * c)) = 1152 - 144 * c) by lia.
  cbn [json_objs] in JO. cbv zeta in JO.
  destruct (negb (at_byte B i 123)) eqn:A123; cbv beta iota in JO; [discriminate JO|].
  assert (A123' : at_byte B i 123 = true) by (destruct (at_byte B i 123); [reflexivity|discriminate A123]).
  match type of JO with
  | context [match ?x with _ => _ end] => destruct x as [[i2 o']|] eqn:JR
  end; cbv beta iota in JO; [|discriminate JO].
  replace (c <? 9) with true in JO by (symmetry; apply Z.ltb_lt; lia).
  pose proof (ws_ge B (i + 1) ltac:(lia)) as G1.
  assert (Hi2 : i < i2).
  { destruct (at_byte B (json_ws B (i + 1)) 125); cbv beta iota in JR.
    - injection JR; intros; subst. lia.
    - pose proof (json_pairs_gt B _ _ _ _ _ JR ltac:(lia)). lia. }
  pose proof (munch_refl [(lo, X); (X + 192, X + 200); (X + 216, X + 224); (X + 992, X + 1012); (X + 1024, X + 2320);
              (X + 2320, X + 2340)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  eapply evt_cut.
  { eapply (obj_head JS JT) with (lo := lo) (X := X) (b := b) (c := c) (i := i) (i2 := i2) (now := now) (B := B)
      (o' := o') (jk := jk) (vpk := vpk) (jv := jv) (vpad := vpad) (j216 := j216) (j192 := j192);
      first [eassumption | reflexivity | lia]. }
  intros ms' (ra1 & t01 & t11 & t21 & a01 & a11 & a21 & a31 & a41 & a51 & a61 & a71 & s91 & s101 & t31 & t41 & t51 &
              t61 & m1 & jk1 & jv1 & j2161 & j1921 & E & MU1 & WM1 & MI1 & ST1 & CO1 & CK1 & CJ1 & C2161 & C1921).
  subst ms'. transport_after_call rsegs m m1 MU1 WM1. clear MU1 WM1 MI.
  assert (CA1 : rw_cells rsegs m1 (X + 1024) [CB (Z.to_nat (144 * (c + 1))) (objs_bytes b vpad (acc ++ [o']))]).
  { rewrite objs_bytes_snoc. replace (Z.to_nat (144 * (c + 1))) with (Z.to_nat (144 * c) + 144)%nat by lia.
    apply cb_join; [exact CA|]. eapply rw_addr; [exact CO1|lia]. }
  clear CA CO1.
  destruct (at_byte B (json_ws B i2) 44) eqn:A44; cbv beta iota in JO.
  - pose proof (jobjs_first _ _ _ _ _ _ _ JO) as A123n.
    pose proof (ws_ge B i2 ltac:(lia)) as G2. pose proof (ws_ge B (json_ws B i2 + 1) ltac:(lia)) as G3.
    eapply evt_cut.
    { eapply obj_tail with (X := X) (b := b) (c := c) (i2 := i2) (B := B) (jr := jr);
        first [eassumption | reflexivity | lia | (left; split; assumption)]. }
    intros ms' [(a0x & a1x & a2x & a3x & A44' & E) |
                (ra2 & t02 & t12 & t22 & a02 & a12 & a22 & a32 & a42 & a52 & a62 & a72 & t32 & t42 & t52 & t62 & m2 &
                 A44' & E & MU2 & WM2 & MI2 & CZ & CR2)]; [rewrite A44 in A44'; discriminate A44'|].
    subst ms'. transport_after_call rsegs m1 m2 MU2 WM2. clear MU2 WM2 MI1.
    assert (CO2 : rw_cells rsegs m2 (X + 1024 + 144 * (c + 1)) [CB 144 (repeat (Z_to_bv 8 0) 144)])
      by (eapply rw_addr; [exact CZ|lia]).
    assert (CR3 : rw_cells rsegs m2 (X + 1168 + 144 * (c + 1)) [CB (Z.to_nat (1152 - 144 * (c + 1))) (skipn 144 jr)]).
    { replace (Z.to_nat (1152 - 144 * (c + 1))) with (Z.to_nat (1008 - 144 * c)) by lia.
      eapply rw_addr; [exact CR2|lia]. }
    clear CZ CR2. pose proof CJ1 as CJw. apply ser_cb in CJw as (Ljv1 & _ & _).
    eapply evt_cut.
    { eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 lo X b (c + 1)
                (json_ws B (json_ws B i2 + 1)) count now B (acc ++ [o']) os jk1 vpk jv1 vpad j2161 j1921 (skipn 144 jr));
        first [eassumption | reflexivity | lia]. }
    intros ms' (ra3 & t03 & t13 & t23 & s13 & a03 & a13 & a23 & a33 & a43 & a53 & a63 & a73 & s53 & s93 & s103 &
                t33 & t43 & t53 & t63 & m3 & jk3 & jv3 & j2163 & j1923 & jo3 & E & MU3 & WM3 & MI3 & ST3 & CA3 & CR4 &
                CK3 & CJ3 & C2163 & C1923).
    subst ms'. transport_after_call rsegs m2 m3 MU3 WM3. clear MU3 WM3 MI2.
    apply evt_done. do 20 eexists. exists m3, jk3, jv3, j2163, j1923, jo3.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI3|]. split; [exact ST3|].
    split; [exact CA3|]. split; [exact CR4|]. split; [exact CK3|]. split; [exact CJ3|]. split; [exact C2163|exact C1923].
  - destruct (at_byte B (json_ws B i2) 93) eqn:A93; cbv beta iota in JO; [|discriminate JO].
    destruct (json_ws B (json_ws B i2 + 1) =? jlen B) eqn:EW; cbv beta iota in JO; [|discriminate JO].
    apply Z.eqb_eq in EW. injection JO as Ecount Eos. subst count os.
    eapply evt_cut.
    { eapply obj_tail with (X := X) (b := b) (c := c) (i2 := i2) (B := B) (jr := jr);
        first [eassumption | reflexivity | lia | (right; split; [|split]; assumption)]. }
    intros ms' [(a0x & a1x & a2x & a3x & A44' & E) |
                (ra2 & t02 & t12 & t22 & a02 & a12 & a22 & a32 & a42 & a52 & a62 & a72 & t32 & t42 & t52 & t62 & m2 &
                 A44' & E & MU2 & WM2 & MI2 & CZ & CR2)]; [|rewrite A44 in A44'; discriminate A44'].
    subst ms'. apply evt_done. do 20 eexists. exists m1, jk1, jv1, j2161, j1921, jr.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI1|]. split; [exact ST1|].
    split; [exact CA1|]. split.
    { replace (Z.to_nat (1296 - 144 * (c + 1))) with (Z.to_nat (1152 - 144 * c)) by lia.
      eapply rw_addr; [exact CR|lia]. }
    split; [exact CK1|]. split; [exact CJ1|]. split; [exact C2161|exact C1921].
Qed.
