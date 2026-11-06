From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge Arr.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require Import StdioModel bcmp_c
  pcap_source_struct pcap_source_struct_next pcap_source_next_lib.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot Require Import PWalkDef.
Import ListNotations.
Open Scope Z_scope.

(* Answers of pcap_source_next are signed: -1 <= n < 2^26. *)
Lemma lts0_wz : forall n, -1 <= n < 2 ^ 26 -> bv_lts (Z_to_bv 64 0) (Z_to_bv 64 n) = (0 <? n).
Proof.
  intros n Hn. rewrite bv_lts_zero_l, unsigned_lit_wrap. destruct (Z.ltb_spec n 0) as [N|N].
  - assert (n = -1) by lia. subst n. reflexivity.
  - rewrite Z.mod_small by lia. rewrite (proj2 (Z.ltb_lt n (2 ^ 63))) by lia. rewrite andb_true_r. reflexivity.
Qed.

(* State at K4 (0x12dcc) after D: the first answer n0 > 0. *)
Definition QDk (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s4 s6 s7 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word)
    (fc : bv 32) (m : word -> option byte) (lo sp_h n0 buf : Z) (ms' : machine_state) : Prop :=
  exists (a0' s5' s11' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' (wz 0) (wz n0) a3 a4 a5 a6 a7 s2 (wz n0) s4 s5' s6 s7 (wz 24) (wz 0)
                  s10 s11' t3 t4 t5 t6) F (Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x1c8)%Z)) fc None m' (seg_rom rsegs) /\
    s5' = wz 0xff00 /\ s11' = wz (1000000 * 2 ^ 32) /\
    munch [(sp_h + 16, sp_h + 24)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (sp_h + 160) /\
    rw_cells rsegs m' (sp_h + 16) [C8 (wz (buf + 12))].

Lemma pcap_D_x : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                          t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
                          (lo sp_h n0 buf : Z) (v16 : word),
  bv_unsigned sp = sp_h -> a0 = wz n0 -> -1 <= n0 < 2 ^ 26 -> s2 = wz buf ->
  rw_cells rsegs m (sp_h + 16) [C8 v16] -> mem_inv rsegs m -> stk rsegs m lo (sp_h + 160) ->
  evt rsegs
    (fun ms' =>
       (0 < n0 /\ QDk ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s4 s6 s7 s10 t3 t4 t5 t6 F fc m lo sp_h n0 buf ms') \/
       (n0 <= 0 /\
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (wz n0) a3 a4 a5 a6 a7 s2 (wz n0) s4 s5 s6 s7 (wz 24) s9
                      s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x458)%Z)) fc None m (seg_rom rsegs)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x198)%Z)) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo sp_h n0 buf v16 HSP E0 Hn E2 H16 MI ST.
  subst sp_h a0 s2.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  step. step.
  rewrite lts0_wz by lia.
  destruct (Z.ltb_spec 0 n0) as [P|P]; cbn [negb]; cbv iota.
  - pose proof (munch_refl [(bv_unsigned sp + 16, bv_unsigned sp + 24)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    do 10 step.
    let mm := cur_mem in
    apply evt_done; left; split; [exact P|]; unfold QDk; do 3 eexists; exists mm.
    split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    exact H16.
  - do 2 step.
    apply evt_done. right. split; [exact P | reflexivity].
Qed.

Lemma pcap_L2_x : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                          t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (n : Z),
  a0 = wz n -> -1 <= n < 2 ^ 26 ->
  evt rsegs
    (fun ms' =>
       (0 < n /\
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 s3 (wz n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
                      s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x1c8)%Z)) fc None m (seg_rom rsegs)) \/
       (n <= 0 /\
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 s3 (wz n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
                      s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x458)%Z)) fc None m (seg_rom rsegs)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x440)%Z)) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m n E0 Hn.
  subst a0.
  do 3 step.
  rewrite lts0_wz by lia.
  destruct (Z.ltb_spec 0 n) as [P|P]; cbv iota.
  - apply evt_done. left. split; [exact P | reflexivity].
  - step. apply evt_done. right. split; [exact P | reflexivity].
Qed.

(* Facts of the record kinds the walk meets. *)
Ltac kind_inv H :=
  revert H; unfold kind, flen, incl;
  repeat match goal with
  | |- context [if (?x =? ?y) then _ else _] => destruct (Z.eqb_spec x y)
  | |- context [if (?x <? ?y) then _ else _] => destruct (Z.ltb_spec x y)
  | |- context [if (?x <=? ?y) then _ else _] => destruct (Z.leb_spec x y)
  end; let K := fresh "Hk" in intros K; cbv iota in K; try discriminate K.

Lemma kind_fit_facts : forall sw F cap q, kind sw F cap q = KFit ->
  16 <= Z.of_nat (length F) - q /\ 1 <= incl sw F q <= cap /\ q + 16 + incl sw F q <= Z.of_nat (length F).
Proof. intros sw F cap q HK. pose proof (hw_range sw F q 8) as R. unfold incl in *. kind_inv HK; lia. Qed.

Lemma kind_empty_facts : forall sw F cap q, kind sw F cap q = KEmpty ->
  16 <= Z.of_nat (length F) - q /\ incl sw F q = 0.
Proof. intros sw F cap q HK. pose proof (hw_range sw F q 8) as R. unfold incl in *. kind_inv HK; lia. Qed.

Lemma kind_big_facts : forall sw F cap q, kind sw F cap q = KBig ->
  16 <= Z.of_nat (length F) - q /\ cap < incl sw F q /\ q + 16 + incl sw F q <= Z.of_nat (length F).
Proof. intros sw F cap q HK. pose proof (hw_range sw F q 8) as R. unfold incl in *. kind_inv HK; lia. Qed.

Lemma skips_le : forall sw F cap q Q, skips sw F cap q Q -> q <= Q.
Proof.
  intros sw F cap q Q HS. induction HS as [q|q Q K HS IH|q Q K HS IH]; [lia | lia |].
  pose proof (hw_range sw F q 8) as R. unfold incl in *. lia.
Qed.

(* The skip loop 0x12dfc-0x12e6c: it passes the KEmpty and KBig records and stops at the record Q (KFit). *)
Lemma pcap_L_skip : forall (sw : bool) (Fc : list byte) (cap q Q : Z), skips sw Fc cap q Q ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (b swz : Z),
  s8 = wz q -> a0 = wz (Z.of_nat (length Fc)) -> a1 = wz (q + 16) -> s4 = wz b -> s1 = wz cap ->
  s5 = wz 0xff00 -> s10 = wz swz -> sw = (swz =? 1) -> (swz = 0 \/ swz = 1) ->
  0 <= q -> q + 16 <= Z.of_nat (length Fc) -> 0 <= cap <= 2040 -> kind sw Fc cap Q = KFit ->
  Z.of_nat (length Fc) < 2 ^ 26 -> bytes_at rsegs m b Fc ->
  evt rsegs
    (fun ms' => exists (s0' a1' a3' a4' a5' a6' a7' s7' : word),
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0' s1 a0 a1' a2 a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7' (wz Q) s9 s10 s11
                     t3 t4 t5 t6) F (Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x26c)%Z)) fc None m (seg_rom rsegs) /\
       s0' = wz (b + Q) /\ a1' = wz (Q + 16) /\ a3' = wz (incl sw Fc Q) /\ s7' = wz (bv_swrap 32 (incl sw Fc Q)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x1f8)%Z)) fc None m (seg_rom rsegs)).
Proof.
  intros sw Fc cap q Q SK. induction SK as [q K1 K2|q Q KE SK IH|q Q KB SK IH];
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m b swz E8 E0 E1 E4 E1c E5 E10 ESW HSW Hq0 Hq16 HC KQ HN HB;
  subst s8 a0 a1 s4 s1 s5 s10; unfold wz in *;
  pose proof (bytes_at_bound rsegs _ _ _ HB) as BB;
  pose proof (kind_fit_facts _ _ _ _ KQ) as (KQ1 & KQ2 & KQ3);
  pose proof (hw_range sw Fc q 8) as RI; change (hw sw Fc q 8) with (incl sw Fc q) in RI;
  pose proof (bytes_at_byte m b Fc (q + 8) HB ltac:(lia)) as HB8;
  pose proof (bytes_at_byte m b Fc (q + 9) HB ltac:(lia)) as HB9;
  pose proof (bytes_at_byte m b Fc (q + 10) HB ltac:(lia)) as HB10;
  pose proof (bytes_at_byte m b Fc (q + 11) HB ltac:(lia)) as HB11;
  assert (EC : bv_unsigned (Z_to_bv 64 cap) = cap) by (apply unsigned_lit; lia);
  assert (EI : bv_unsigned (Z_to_bv 64 (incl sw Fc q)) = incl sw Fc q) by (apply unsigned_lit; lia);
  step;
  (destruct HSW as [SW|SW]; subst swz;
   [do 11 step; if_true | do 11 step; if_false; do 8 step]);
  rep_reg 23 (Z_to_bv 64 (bv_swrap 32 (incl sw Fc q))) ltac:(rewrite ESW; hw_eq);
  do 2 step; rewrite zx32_val, uns_swrap_mod32_0 by lia;
  step; rewrite eqb_swrap0 by lia.
  (* skips_stop: the record at q is KFit *)
  1-2: rewrite (proj2 (Z.eqb_neq _ _)) by lia; cbv iota; step; if_true;
       apply evt_done; do 8 eexists; split; [reflexivity|]; unfold wz; repeat split.
  (* skips_empty *)
  1-2: pose proof (kind_empty_facts _ _ _ _ KE) as (KE1 & KE2);
       rewrite (proj2 (Z.eqb_eq _ _)) by lia; cbv iota; do 3 step.
  (* skips_big *)
  3-4: pose proof (kind_big_facts _ _ _ _ KB) as (KB1 & KB2 & KB3);
       rewrite (proj2 (Z.eqb_neq _ _)) by lia; cbv iota; step; if_false; do 3 step.
  all: pose proof (skips_le _ _ _ _ _ SK) as LQ;
       assert (EF : bv_unsigned (Z_to_bv 64 (Z.of_nat (length Fc))) = Z.of_nat (length Fc)) by (apply unsigned_lit; lia);
       assert (EA : bv_unsigned (Z_to_bv 64 (q + incl sw Fc q + 32)) = q + incl sw Fc q + 32) by (apply unsigned_lit; lia);
       step; if_false; step;
       (eapply IH; first [ reflexivity | exact ESW | exact KQ | exact HN | exact HB | (left; reflexivity)
                         | (right; reflexivity) | (unfold wz; f_equal; lia) | lia ]).
Qed.
