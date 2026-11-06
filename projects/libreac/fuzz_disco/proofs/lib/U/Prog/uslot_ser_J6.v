From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge FP Image.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model disco_json_reader_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_ser_defs slot_ser_tokb slot_ser_ws slot_ser_J0 slot_ser_J2 slot_ser_J6.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import slot_inv slot_lib printf_facts_c json_scalar_c jtok_is_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import uslot_ser_tokb uslot_ser_ws uslot_ser uslot_ser_Pq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import uslot_ser_J1 uslot_ser_J2 uslot_ser_J3 uslot_ser_J4 uslot_ser_J5.
Import ListNotations.
Open Scope Z_scope.

Lemma uobj_body : json_scalar_contract -> jtok_is_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (lo X b c i i2 : Z) (B : list Z) (o' : jobj) (jk vpk jv vpad jo j208 j232 j240 j248 : list byte),
  sp = Z_to_bv 64 X -> s1 = Z_to_bv 64 (nt b) -> s2 = Z_to_bv 64 WS_MASK -> s3 = Z_to_bv 64 b ->
  s4 = Z_to_bv 64 (jlen B) -> s6 = Z_to_bv 64 i -> s8 = Z_to_bv 64 (X + 2368) -> s9 = Z_to_bv 64 c ->
  s10 = Z_to_bv 64 32 -> s11 = Z_to_bv 64 1 ->
  X mod 16 = 0 -> 0 <= c <= 8 -> 0 <= i -> at_byte B i 123 = true ->
  (if at_byte B (json_ws B (i + 1)) 125 then Some (json_ws B (i + 1) + 1, jobj_empty)
   else json_pairs B (json_ws B (i + 1)) jobj_empty (length B)) = Some (i2, o') ->
  length vpk = 4%nat -> length vpad = 4%nat -> length jv = 20%nat ->
  0 < b -> b + jlen B + 1 <= lo -> Forall (fun c => 0 <= c < 256) B -> bytes_at rsegs m b (pf_bytes (B ++ [0])) ->
  rw_cells rsegs m (X + 176) [C8 (Z_to_bv 64 (nt (X + 1056)))] ->
  rw_cells rsegs m (X + 208) [CB 8 j208] -> rw_cells rsegs m (X + 232) [CB 8 j232] ->
  rw_cells rsegs m (X + 240) [CB 8 j240] -> rw_cells rsegs m (X + 248) [CB 8 j248] ->
  rw_cells rsegs m (X + 1024) [CB 20 jk] -> rw_cells rsegs m (X + 1044) [CB 4 vpk] ->
  rw_cells rsegs m (X + 1056 + 144 * c) [CB 144 jo] ->
  rw_cells rsegs m (X + 2352) [CB 20 jv] -> rw_cells rsegs m (X + 2372) [CB 4 vpad] ->
  bytes_at rsegs m JSON_SCALAR_L js_table -> mem_inv rsegs m -> stk rsegs m lo X -> lo + 112 <= X -> 0x524f8 <= lo ->
  X + 2624 < 2 ^ 63 ->
  evt rsegs
    (fun ms' => exists (ra' t0' t1' t2' s0' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' : word)
                       (m' : word -> option byte) (jk' jv' j208' j232' j240' j248' : list byte),
       ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0' s1 a0' a1' a2' a3' a4' a5' a6' a7'
                     s2 s3 s4 s5' (Z_to_bv 64 (i2 - 1)) s7' s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x13b74) fc None m' (seg_rom rsegs) /\
       munch [(lo, X); (X + 208, X + 216); (X + 232, X + 256); (X + 1024, X + 1044);
              (X + 1056 + 144 * c, X + 1200 + 144 * c); (X + 2352, X + 2372)] m m' /\
       wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo X /\
       rw_cells rsegs m' (X + 208) [CB 8 j208'] /\ rw_cells rsegs m' (X + 232) [CB 8 j232'] /\
       rw_cells rsegs m' (X + 240) [CB 8 j240'] /\ rw_cells rsegs m' (X + 248) [CB 8 j248'] /\
       rw_cells rsegs m' (X + 1024) [CB 20 jk'] /\
       rw_cells rsegs m' (X + 1056 + 144 * c) [CB 144 (obj_bytes b vpad o')] /\
       rw_cells rsegs m' (X + 2352) [CB 20 jv'])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1386c) fc None m (seg_rom rsegs)).
Proof.
  intros JS JT ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo X b c i i2 B o' jk vpk jv vpad jo j208 j232 j240 j248 Esp Es1 Es2 Es3 Es4 Es6 Es8 Es9 Es10 Es11
    HX16 Hc Hi A123 JP Lk Lv Ljv Hb Hbl FB BB C176 C208 C232 C240 C248 CK CV CO CJ CP JTB MI ST HK HI HX.
  assert (Hc8 : (X + 1056 + 144 * c) mod 8 = 0) by (clear - HX16; Z.div_mod_to_equations; lia).
  subst sp s1 s2 s3 s4 s6 s8 s9 s10 s11.
  pose proof (munch_refl [(lo, X); (X + 208, X + 216); (X + 232, X + 256); (X + 1024, X + 1044);
              (X + 1056 + 144 * c, X + 1200 + 144 * c); (X + 2352, X + 2372)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  eapply evt_cut.
  { eapply (uobj_head JS) with (lo := lo) (X := X) (b := b) (c := c) (i := i) (i2 := i2) (B := B) (o' := o')
      (jk := jk) (vpk := vpk) (jv := jv) (vpad := vpad) (jo := jo) (j208 := j208) (j232 := j232) (j240 := j240)
      (j248 := j248); first [eassumption | reflexivity | lia]. }
  intros ms' [(ra1 & t01 & t11 & t21 & a01 & a11 & a21 & a31 & a41 & a51 & a61 & a71 & t31 & t41 & t51 & t61 & m1 &
               E & MU1 & WM1 & MI1 & ST1 & CO1) |
              (ra1 & t01 & t11 & t21 & a11 & a21 & a31 & a41 & a51 & a61 & a71 & t31 & t41 & t51 & t61 & m1 &
               j & ks & kl & f & Hi1 & JS1 & JP1 & E & MU1 & WM1 & MI1 & ST1 & BB1 & CK1 & CV1 & C2401 & C2481 &
               C2321 & C2081 & CO1 & CJ1 & CP1 & JTB1)].
  - subst ms'. transport_after_call rsegs m m1 MU1 WM1. clear MU1 WM1 MI.
    apply evt_done. do 19 eexists. exists m1, jk, jv, j208, j232, j240, j248.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI1|]. split; [exact ST1|].
    split; [exact C208|]. split; [exact C232|]. split; [exact C240|]. split; [exact C248|].
    split; [exact CK|]. split; [exact CO1|exact CJ].
  - subst ms'. transport_after_call rsegs m m1 MU1 WM1. clear MU1 WM1 MI.
    eapply evt_cut.
    { eapply (ukey_loop JS JT (S f)) with (lo := lo) (X := X) (b := b) (cur := X + 1056 + 144 * c)
        (i := json_ws B (i + 1)) (j := j) (ks := ks) (kl := kl) (r := i2) (B := B) (o := jobj_empty) (o' := o')
        (f := f) (vpk := vpk) (vpad := vpad) (jv := jv) (m0 := m1);
        first [eassumption | reflexivity | lia | apply munch_refl | apply wmono_refl | apply jobj_empty_inb]. }
    intros ms' (ra2 & t02 & t12 & t22 & a02 & a12 & a22 & a32 & a42 & a52 & a62 & a72 & t32 & t42 & t52 & t62 & m2 &
                jk2 & jv2 & E & MU2 & WM2 & MI2 & ST2 & CO2 & CK2 & CJ2).
    subst ms'. transport_after_call rsegs m1 m2 MU2 WM2. clear MU2 WM2 MI1.
    step.
    apply evt_done. do 19 eexists.
    exists m2, jk2, jv2, (le8 (Z_to_bv 64 (X + 1056 + 144 * c + 120))), (le8 (Z_to_bv 64 (X + 1056 + 144 * c + 96))),
      (le8 (Z_to_bv 64 c)), (le8 (Z_to_bv 64 (X + 1056 + 144 * c + 72))).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI2|]. split; [exact ST2|].
    split; [apply user_c8; assumption|]. split; [apply user_c8; assumption|].
    split; [apply user_c8; assumption|]. split; [apply user_c8; assumption|].
    split; [exact CK2|]. split; [exact CO2|exact CJ2].
Qed.

Lemma uobj_loop : json_scalar_contract -> jtok_is_contract ->
  forall (f : nat) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (lo X b c i count : Z) (B : list Z) (acc os : list jobj) (jk vpk jv vpad jo j208 j232 j240 j248 : list byte),
  sp = Z_to_bv 64 X -> s1 = Z_to_bv 64 (nt b) -> s2 = Z_to_bv 64 WS_MASK -> s3 = Z_to_bv 64 b ->
  s4 = Z_to_bv 64 (jlen B) -> s6 = Z_to_bv 64 i -> s8 = Z_to_bv 64 (X + 2368) -> s9 = Z_to_bv 64 c ->
  s10 = Z_to_bv 64 32 -> s11 = Z_to_bv 64 1 ->
  X mod 16 = 0 -> 0 <= c -> 0 <= i -> json_objs B i c 9 acc f = Some (count, os) -> count <= 8 ->
  length vpk = 4%nat -> length vpad = 4%nat -> length jv = 20%nat ->
  0 < b -> b + jlen B + 1 <= lo -> Forall (fun c => 0 <= c < 256) B -> bytes_at rsegs m b (pf_bytes (B ++ [0])) ->
  rw_cells rsegs m (X + 176) [C8 (Z_to_bv 64 (nt (X + 1056)))] ->
  rw_cells rsegs m (X + 208) [CB 8 j208] -> rw_cells rsegs m (X + 216) [C8 (Z_to_bv 64 IMAX)] ->
  rw_cells rsegs m (X + 232) [CB 8 j232] -> rw_cells rsegs m (X + 240) [CB 8 j240] ->
  rw_cells rsegs m (X + 248) [CB 8 j248] ->
  rw_cells rsegs m (X + 1024) [CB 20 jk] -> rw_cells rsegs m (X + 1044) [CB 4 vpk] ->
  rw_cells rsegs m (X + 1056) [CB (Z.to_nat (144 * c)) (objs_bytes b vpad acc)] ->
  rw_cells rsegs m (X + 1056 + 144 * c) [CB (Z.to_nat (1296 - 144 * c)) jo] ->
  rw_cells rsegs m (X + 2352) [CB 20 jv] -> rw_cells rsegs m (X + 2372) [CB 4 vpad] ->
  bytes_at rsegs m JSON_SCALAR_L js_table -> mem_inv rsegs m -> stk rsegs m lo X -> lo + 112 <= X -> 0x524f8 <= lo ->
  X + 2624 < 2 ^ 63 ->
  evt rsegs
    (fun ms' => exists (ra' t0' t1' t2' s0' a0' a1' a2' a3' a4' a5' a6' a7' s5' s6' s7' t3' t4' t5' t6' : word)
                       (m' : word -> option byte) (jk' jv' jo' j208' j232' j240' j248' : list byte),
       ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0' s1 a0' a1' a2' a3' a4' a5' a6' a7'
                     s2 s3 s4 s5' s6' s7' s8 (Z_to_bv 64 count) s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x13f08) fc None m' (seg_rom rsegs) /\
       munch [(lo, X); (X + 208, X + 216); (X + 232, X + 256); (X + 1024, X + 1044); (X + 1056, X + 2372)] m m' /\
       wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo X /\
       rw_cells rsegs m' (X + 208) [CB 8 j208'] /\ rw_cells rsegs m' (X + 232) [CB 8 j232'] /\
       rw_cells rsegs m' (X + 240) [CB 8 j240'] /\ rw_cells rsegs m' (X + 248) [CB 8 j248'] /\
       rw_cells rsegs m' (X + 1024) [CB 20 jk'] /\ rw_cells rsegs m' (X + 1044) [CB 4 vpk] /\
       rw_cells rsegs m' (X + 1056) [CB (Z.to_nat (144 * count)) (objs_bytes b vpad os)] /\
       rw_cells rsegs m' (X + 1056 + 144 * count) [CB (Z.to_nat (1296 - 144 * count)) jo'] /\
       rw_cells rsegs m' (X + 2352) [CB 20 jv'] /\ rw_cells rsegs m' (X + 2372) [CB 4 vpad])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1386c) fc None m (seg_rom rsegs)).
Proof.
  intros JS JT f. induction f as [|f IH];
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
      lo X b c i count B acc os jk vpk jv vpad jo j208 j232 j240 j248
      Esp Es1 Es2 Es3 Es4 Es6 Es8 Es9 Es10 Es11 HX16 Hc Hi JO Hcnt Lk Lv Ljv Hb Hbl FB BB
      C176 C208 C216 C232 C240 C248 CK CV CA CR CJ CP JTB MI ST HK HI HX; [discriminate JO|].
  pose proof (json_objs_lt B (S f) i c 9 acc count os JO) as Hlt.
  assert (HJL : JSON_SCALAR_L = 0x205e0) by reflexivity.
  assert (LJS : Z.of_nat (length js_table) = 24) by reflexivity.
  assert (LBB : Z.of_nat (length (pf_bytes (B ++ [0]))) = jlen B + 1)
    by (rewrite ulength_pf_bytes, length_app; unfold jlen; cbn [length]; lia).
  pose proof CR as CRw. apply user_cb in CRw as (LR & _ & _).
  destruct (user_split m (X + 1056 + 144 * c) (X + 1200 + 144 * c) 144 (Z.to_nat (1152 - 144 * c))
              (Z.to_nat (1296 - 144 * c)) jo ltac:(lia) ltac:(lia) CR) as [CR1 CR2]. clear CR.
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
  pose proof (munch_refl [(lo, X); (X + 208, X + 216); (X + 232, X + 256); (X + 1024, X + 1044);
              (X + 1056, X + 2372)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  eapply evt_cut.
  { eapply (uobj_body JS JT) with (lo := lo) (X := X) (b := b) (c := c) (i := i) (i2 := i2) (B := B) (o' := o')
      (jk := jk) (vpk := vpk) (jv := jv) (vpad := vpad) (jo := firstn 144 jo) (j208 := j208) (j232 := j232)
      (j240 := j240) (j248 := j248); first [eassumption | reflexivity | lia]. }
  intros ms' (ra1 & t01 & t11 & t21 & s01 & a01 & a11 & a21 & a31 & a41 & a51 & a61 & a71 & s51 & s71 & t31 & t41 &
              t51 & t61 & m1 & jk1 & jv1 & j2081 & j2321 & j2401 & j2481 & E & MU1 & WM1 & MI1 & ST1 &
              C2081 & C2321 & C2401 & C2481 & CK1 & CO1 & CJ1).
  subst ms'. transport_after_call rsegs m m1 MU1 WM1. clear MU1 WM1 MI.
  assert (CA1 : rw_cells rsegs m1 (X + 1056) [CB (Z.to_nat (144 * (c + 1))) (objs_bytes b vpad (acc ++ [o']))]).
  { rewrite objs_bytes_snoc. replace (Z.to_nat (144 * (c + 1))) with (Z.to_nat (144 * c) + 144)%nat by lia.
    apply ucb_join; [exact CA|]. eapply urw_addr; [exact CO1|lia]. }
  assert (CR3 : rw_cells rsegs m1 (X + 1056 + 144 * (c + 1)) [CB (Z.to_nat (1296 - 144 * (c + 1))) (skipn 144 jo)]).
  { replace (Z.to_nat (1296 - 144 * (c + 1))) with (Z.to_nat (1152 - 144 * c)) by lia.
    eapply urw_addr; [exact CR2|lia]. }
  clear CA CO1 CR2.
  pose proof CJ1 as CJw. apply user_cb in CJw as (Ljv1 & _ & _).
  pose proof (ws_ge B i2 ltac:(lia)) as G2.
  destruct (at_byte B (json_ws B i2) 44) eqn:A44; cbv beta iota in JO.
  - pose proof (jobjs_first _ _ _ _ _ _ _ JO) as A123n.
    pose proof (ws_ge B (json_ws B i2 + 1) ltac:(lia)) as G3.
    eapply evt_cut.
    { eapply uobj_tail_e with (X := X) (b := b) (count := c) (i2 := i2) (B := B);
        first [eassumption | reflexivity | lia | (unfold IMAX; lia) | (left; split; assumption)]. }
    intros ms' [(a0x & a1x & A44' & E) | (a0x & a1x & A44' & E)]; [rewrite A44 in A44'; discriminate A44'|].
    subst ms'.
    eapply evt_cut.
    { eapply IH with (lo := lo) (X := X) (b := b) (c := c + 1) (i := json_ws B (json_ws B i2 + 1)) (count := count)
        (B := B) (acc := acc ++ [o']) (os := os) (jk := jk1) (vpk := vpk) (jv := jv1) (vpad := vpad)
        (jo := skipn 144 jo) (j208 := j2081) (j232 := j2321) (j240 := j2401) (j248 := j2481);
        first [eassumption | reflexivity | lia]. }
    intros ms' (ra3 & t03 & t13 & t23 & s03 & a03 & a13 & a23 & a33 & a43 & a53 & a63 & a73 & s53 & s63 & s73 &
                t33 & t43 & t53 & t63 & m3 & jk3 & jv3 & jo3 & j2083 & j2323 & j2403 & j2483 & E & MU3 & WM3 & MI3 &
                ST3 & C2083 & C2323 & C2403 & C2483 & CK3 & CV3 & CA3 & CR4 & CJ3 & CP3).
    subst ms'. transport_after_call rsegs m1 m3 MU3 WM3. clear MU3 WM3 MI1.
    apply evt_done. do 20 eexists. exists m3, jk3, jv3, jo3, j2083, j2323, j2403, j2483.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI3|]. split; [exact ST3|].
    split; [exact C2083|]. split; [exact C2323|]. split; [exact C2403|]. split; [exact C2483|].
    split; [exact CK3|]. split; [exact CV3|]. split; [exact CA3|]. split; [exact CR4|]. split; [exact CJ3|exact CP3].
  - destruct (at_byte B (json_ws B i2) 93) eqn:A93; cbv beta iota in JO; [|discriminate JO].
    destruct (json_ws B (json_ws B i2 + 1) =? jlen B) eqn:EW; cbv beta iota in JO; [|discriminate JO].
    apply Z.eqb_eq in EW. injection JO as Ecount Eos. subst count os.
    eapply evt_cut.
    { eapply uobj_tail_e with (X := X) (b := b) (count := c) (i2 := i2) (B := B);
        first [eassumption | reflexivity | lia | (unfold IMAX; lia) | (right; split; [|split]; assumption)]. }
    intros ms' [(a0x & a1x & A44' & E) | (a0x & a1x & A44' & E)]; [|rewrite A44 in A44'; discriminate A44'].
    subst ms'. apply evt_done. do 20 eexists. exists m1, jk1, jv1, (skipn 144 jo), j2081, j2321, j2401, j2481.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI1|]. split; [exact ST1|].
    split; [exact C2081|]. split; [exact C2321|]. split; [exact C2401|]. split; [exact C2481|].
    split; [exact CK1|]. split; [exact CV|]. split; [exact CA1|]. split; [exact CR3|]. split; [exact CJ1|exact CP].
Qed.
