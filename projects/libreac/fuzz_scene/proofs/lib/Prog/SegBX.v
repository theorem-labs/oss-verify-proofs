From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes Image Arr.
From OSSVerify.Proofs.libreac.fuzz_scene.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog Require Import SceneTac.
Import ListNotations.
Open Scope Z_scope.

Set Printing Width 3000.
Ltac show_g := match goal with |- evt _ _ (MS ?R _ ?pc _ _ ?m _) => idtac "PC:" pc "MEM:" m | |- ?G => idtac "GOAL:" G end.
Ltac show_r := match goal with |- evt _ _ (MS ?R _ ?pc _ _ ?m _) => idtac "REGS:" R end.

Definition TADDR : Z := 0x103ae.
Definition nbE (n : Z) : Z := if n =? 0 then 1 else n.
Definition sx16 (v : Z) : Z := if v <? 32768 then v else v - 65536.

Lemma T_read : forall m i, 0 <= i < 8904 -> exists b, ov_read_bytes rsegs m (wa (TADDR + i)) 1 = Some [b].
Proof.
  intros m i Hi.
  assert (Hall : forallb (fun j => match seg_rom rsegs (wa (TADDR + Z.of_nat j)) with Some _ => true | None => false end)
                   (seq 0 (Z.to_nat 8904)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in Hall. specialize (Hall (Z.to_nat i) ltac:(apply in_seq; lia)).
  rewrite Z2Nat.id in Hall by lia.
  rewrite ov_rdn, rdn_unfold. unfold mrd.
  destruct (m (wa (TADDR + i))) as [b|]; [exists b; reflexivity|].
  destruct (seg_rom rsegs (wa (TADDR + i))) as [b|]; [exists b; reflexivity|discriminate].
Qed.

Lemma u8_store : forall (m0 m : word -> option byte) W A bs (k : Z) (bl : list byte),
  u8arr rsegs m A bs -> mem_inv rsegs m -> munch W m0 m -> wmono rsegs m0 m ->
  0 <= k -> k + Z.of_nat (length bl) <= Z.of_nat (length bs) -> inside W (A + k) (Z.of_nat (length bl)) ->
  u8arr rsegs (write_to_mem m (Z_to_bv 64 (A + k)) bl) A (upd_bytes bs (Z.to_nat k) bl) /\
  length (upd_bytes bs (Z.to_nat k) bl) = length bs /\
  mem_inv rsegs (write_to_mem m (Z_to_bv 64 (A + k)) bl) /\
  munch W m0 (write_to_mem m (Z_to_bv 64 (A + k)) bl) /\ wmono rsegs m0 (write_to_mem m (Z_to_bv 64 (A + k)) bl).
Proof.
  intros m0 m W A bs k bl [HB HW] HMI MU WM Hk Hkl Hin.
  pose proof (bytes_at_bound _ _ _ _ HB) as [HA HAl].
  change (Z_to_bv 64 (A + k)) with (wa (A + k)).
  assert (HL : length (upd_bytes bs (Z.to_nat k) bl) = length bs) by (apply upd_bytes_length; lia).
  split; [split|].
  - apply bytes_at_write_inside; [exact HB | lia | lia].
  - rewrite HL. apply wr_at_write. exact HW.
  - split; [exact HL|].
    split; [apply mem_inv_store; [exact HMI | apply wr_at_store_ok with (n := Z.of_nat (length bs)); [exact HW | lia | lia]]|].
    split; [apply munch_write; [exact MU | lia | lia | exact Hin]|].
    apply wmono_write. exact WM.
Qed.

Section S.
Variables (gp tp : word) (F : bvmap 5 word) (fc : bv 32).

Lemma fill_loop : forall (k : nat) (ra sp t0 t1 t2 s0 bd a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (m0 m : word -> option byte) (n i : Z) (bs : list byte),
  Z.of_nat k = n - i -> 0 <= i < n -> bv_unsigned s8 = n ->
  Z.of_nat (length bs) = n -> u8arr rsegs m (bv_unsigned bd) bs ->
  mem_inv rsegs m -> munch [(bv_unsigned bd, bv_unsigned bd + n)] m0 m -> wmono rsegs m0 m ->
  evt rsegs (fun ms' => exists (a0' a3' a4' : word) (m' : word -> option byte) (bs' : list byte),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 bd a0' (Z_to_bv 64 TADDR) (Z_to_bv 64 1112) a3' a4' a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14fe8) fc None m' (seg_rom rsegs) /\
      munch [(bv_unsigned bd, bv_unsigned bd + n)] m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\
      u8arr rsegs m' (bv_unsigned bd) bs' /\ Z.of_nat (length bs') = n)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 bd (Z_to_bv 64 i) (Z_to_bv 64 TADDR) (Z_to_bv 64 1112) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14fc0) fc None m (seg_rom rsegs)).
Proof.
  induction k as [|k IH]; intros ra sp t0 t1 t2 s0 bd a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    m0 m n i bs HK Hi Hs8 Hlen HU HMI MU WM; [lia|].
  pose proof (bv_unsigned_in_range 64 bd) as Rbd. pose proof (bv_unsigned_in_range 64 s8) as Rs8.
  unfold bv_modulus in Rbd, Rs8.
  pose proof (bytes_at_bound _ _ _ _ (proj1 HU)) as [_ HBd].
  unfold TADDR.
  zstep.
  zstep.
  if_cases K; zify_cond K; rewrite Z.shiftr_div_pow2 in K by lia; change (2 ^ 3) with 8 in K.
  all: [> zstep; zstep; zstep
       | destruct (T_read m i ltac:(lia)) as [b HR]; unfold TADDR in HR; zstep; zstep; zstep; zstep; zstep ].
  all: assert (HS : store_ok rsegs m (Z_to_bv 64 (bv_unsigned bd + i)) 1 = true)
      by (apply (u8arr_store_ok rsegs m (bv_unsigned bd) bs i); [exact HU | lia | reflexivity]).
  all: zstep.
  all: match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm (Z_to_bv 64 (?A + ?k)) ?bl) _) =>
      destruct (u8_store m0 mm _ A bs k bl HU HMI MU WM) as (HU' & HL' & HMI' & MU' & WM');
      [lia | simpl_sizes; lia | cbn [inside]; simpl_sizes; lia | ]
    end.
  all: zstep.
  all: if_cases K2; zify_cond K2.
  all: [> eapply IH with (m0 := m0) (n := n) (i := i + 1);
          [lia | lia | exact Hs8 | rewrite HL'; exact Hlen | exact HU' | exact HMI' | exact MU' | exact WM']
       | finish; first [exact HU' | rewrite ?HL'; lia]
       | eapply IH with (m0 := m0) (n := n) (i := i + 1);
          [lia | lia | exact Hs8 | rewrite HL'; exact Hlen | exact HU' | exact HMI' | exact MU' | exact WM']
       | finish; first [exact HU' | rewrite ?HL'; lia] ].
Qed.

Lemma xor_loop : forall (k : nat) (ra sp t0 t1 t2 s0 bd p a1 a2 a3 a4 a5 a6 a7 s2 q s4 s5 e s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (m0 m : word -> option byte) (N K PC i : Z) (bs inb : list byte),
  Z.of_nat k = K - i -> 0 <= i < K -> K <= N -> K <= Z.of_nat (length inb) -> Z.of_nat (length bs) = N ->
  u8arr rsegs m (bv_unsigned bd) bs -> bytes_at rsegs m PC inb ->
  (PC + Z.of_nat (length inb) <= bv_unsigned bd \/ bv_unsigned bd + N <= PC) -> bv_unsigned bd + N < 2 ^ 64 ->
  mem_inv rsegs m -> munch [(bv_unsigned bd, bv_unsigned bd + N)] m0 m -> wmono rsegs m0 m ->
  p = Z_to_bv 64 (bv_unsigned bd + i) -> q = Z_to_bv 64 (PC + i) -> e = Z_to_bv 64 (bv_unsigned bd + K) ->
  evt rsegs (fun ms' => exists (a0' a1' a2' s3' : word) (m' : word -> option byte) (bs' : list byte),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 bd a0' a1' a2' a3 a4 a5 a6 a7
                    s2 s3' s4 s5 e s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x15018) fc None m' (seg_rom rsegs) /\
      munch [(bv_unsigned bd, bv_unsigned bd + N)] m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\
      u8arr rsegs m' (bv_unsigned bd) bs' /\ Z.of_nat (length bs') = N /\ bytes_at rsegs m' PC inb)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 bd p a1 a2 a3 a4 a5 a6 a7 s2 q s4 s5 e s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14ffc) fc None m (seg_rom rsegs)).
Proof.
  induction k as [|k IH]; intros ra sp t0 t1 t2 s0 bd p a1 a2 a3 a4 a5 a6 a7 s2 q s4 s5 e s7 s8 s9 s10 s11 t3 t4 t5 t6
    m0 m N K PC i bs inb HK Hi HKN HKI Hlen HU HIN DJ HBN HMI MU WM Hp Hq He; [lia|].
  subst p q e.
  pose proof (bv_unsigned_in_range 64 bd) as Rbd. unfold bv_modulus in Rbd.
  pose proof (bytes_at_bound _ _ _ _ (proj1 HU)) as [_ HBd].
  pose proof (bytes_at_bound _ _ _ _ HIN) as [HP0 HPd].
  pose proof (bytes_at_byte1 _ _ _ i HIN ltac:(lia)) as HR1.
  zstep.
  pose proof (bytes_at_byte1 _ _ _ i (proj1 HU) ltac:(lia)) as HR2.
  zstep. zstep.
  assert (HS : store_ok rsegs m (Z_to_bv 64 (bv_unsigned bd + i)) 1 = true)
    by (apply (u8arr_store_ok rsegs m (bv_unsigned bd) bs i); [exact HU | lia | reflexivity]).
  zstep.
  match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm (Z_to_bv 64 (?A + ?k)) ?bl) _) =>
      destruct (u8_store m0 mm _ A bs k bl HU HMI MU WM) as (HU' & HL' & HMI' & MU' & WM');
      [lia | simpl_sizes; lia | cbn [inside]; simpl_sizes; lia | ];
      assert (HIN' : bytes_at rsegs (write_to_mem mm (Z_to_bv 64 (A + k)) bl) PC inb)
        by (apply (bytes_at_write_other rsegs mm (A + k) bl PC inb HIN); simpl_sizes; lia)
  end.
  zstep. zstep. zstep.
  if_cases K2; zify_cond K2; rewrite ?Z.mod_small in K2 by lia.
  - eapply IH with (m0 := m0) (N := N) (K := K) (PC := PC) (i := i + 1);
      [lia | lia | lia | lia | rewrite HL'; exact Hlen | exact HU' | exact HIN' | exact DJ | exact HBN | exact HMI'
      | exact MU' | exact WM' | f_equal; lia | f_equal; lia | reflexivity].
  - finish; first [exact HU' | exact HIN' | rewrite ?HL'; lia].
Qed.

Lemma pre_B : forall (ra sp t0 t1 t2 s0 s1 bd a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (m : word -> option byte) (n r PC : Z) (bs inb : list byte),
  0 <= n < 65536 -> bv_unsigned s8 = n -> bv_unsigned s6 = r -> bv_unsigned s3 = PC ->
  bv_unsigned bd <> 0 -> Z.of_nat (length bs) = nbE n -> u8arr rsegs m (bv_unsigned bd) bs ->
  bv_unsigned bd + nbE n < 2 ^ 64 ->
  bytes_at rsegs m PC inb -> Z.of_nat (length inb) = r ->
  (PC + r <= bv_unsigned bd \/ bv_unsigned bd + nbE n <= PC) ->
  bytes_at rsegs m 0x1ef60 (le8 (Z_to_bv 64 TADDR)) -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists (a0' a1' a2' a3' a4' s3' s6' : word) (m' : word -> option byte) (bs' : list byte),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 bd a0' a1' a2' a3' a4' a5 a6 a7 s2 s3' s4 s5 s6' s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x15018) fc None m' (seg_rom rsegs) /\
      munch [(bv_unsigned bd, bv_unsigned bd + nbE n)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
      u8arr rsegs m' (bv_unsigned bd) bs' /\ Z.of_nat (length bs') = nbE n /\ bytes_at rsegs m' PC inb)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 bd a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14fa4) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp t0 t1 t2 s0 s1 bd a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 m n r PC bs inb
    HN Hs8 Hs6 Hs3 Hbd Hlen HU HBN HIN Hr DJ HGOT HMI.
  pose proof (bv_unsigned_in_range 64 bd) as Rbd. pose proof (bv_unsigned_in_range 64 s8) as Rs8.
  pose proof (bv_unsigned_in_range 64 s6) as Rs6. pose proof (bv_unsigned_in_range 64 s3) as Rs3.
  unfold bv_modulus in Rbd, Rs8, Rs6, Rs3.
  pose proof (bytes_at_bound _ _ _ _ HIN) as [HP0 HPd].
  pose proof (munch_refl [(bv_unsigned bd, bv_unsigned bd + nbE n)] m) as MU0.
  pose proof (wmono_refl rsegs m) as WM0.
  zstep. sres_if.
  zstep.
  zstep.
  if_cases K0; zify_cond K0.
  - zstep. sres_if. zstep. zstep. sres_if.
    show_g.
    finish; try eassumption.
  - assert (NB : nbE n = n) by (unfold nbE; destruct (Z.eqb_spec n 0); lia).
    rewrite NB in *.
    assert (HG : ov_read_bytes rsegs m (wa 126816) 8 = Some (le8 (Z_to_bv 64 66478))).
    { pose proof (bytes_at_read rsegs m 126816 _ 0 8 HGOT ltac:(lia) ltac:(rewrite length_le8; lia)) as X.
      rewrite Z.add_0_r in X. rewrite X. f_equal. }
    zstep. zstep. zstep. zstep.
    show_g. show_r.
    eapply evt_cut; [eapply (fill_loop (Z.to_nat n)) with (m0 := m) (n := n) (i := 0) (bs := bs);
      [lia | lia | exact Hs8 | exact Hlen | exact HU | exact HMI | exact MU0 | exact WM0] | ].
    intros ms' (a0' & a3' & a4' & m1 & bs1 & E & MU1 & WM1 & MI1 & HU1 & HL1). subst ms'.
    pose proof (bytes_at_transport rsegs _ m m1 PC inb HIN MU1 ltac:(cbn [disjoint_from]; lia)) as HIN1.
    zstep.
    if_cases K1; zify_cond K1.
    + zstep. if_cases K2; zify_cond K2.
      * finish; try eassumption.
      * zstep. zstep. show_g. show_r.
        eapply evt_cut; [eapply (xor_loop (Z.to_nat r)) with (m0 := m) (N := n) (K := r) (PC := PC) (i := 0) (bs := bs1) (inb := inb);
          [lia | lia | lia | lia | exact HL1 | exact HU1 | exact HIN1 | lia | exact HBN | exact MI1 | exact MU1 | exact WM1
          | rewrite Z.add_0_r; symmetry; apply Z_to_bv_lit_self
          | rewrite Z.add_0_r, <- Hs3; symmetry; apply Z_to_bv_lit_self
          | rewrite <- Hs6; reflexivity ] | ].
        intros ms' (a0'' & a1' & a2' & s3' & m2 & bs2 & E & MU2 & WM2 & MI2 & HU2 & HL2 & HIN2). subst ms'.
        finish; try eassumption.
    + zstep. zstep. sres_if.
      zstep. zstep. show_g. show_r.
      eapply evt_cut; [eapply (xor_loop (Z.to_nat n)) with (m0 := m) (N := n) (K := n) (PC := PC) (i := 0) (bs := bs1) (inb := inb);
        [lia | lia | lia | lia | exact HL1 | exact HU1 | exact HIN1 | lia | exact HBN | exact MI1 | exact MU1 | exact WM1
        | rewrite Z.add_0_r; symmetry; apply Z_to_bv_lit_self
        | rewrite Z.add_0_r, <- Hs3; symmetry; apply Z_to_bv_lit_self
        | rewrite <- Hs8; reflexivity ] | ].
      intros ms' (a0'' & a1' & a2' & s3' & m2 & bs2 & E & MU2 & WM2 & MI2 & HU2 & HL2 & HIN2). subst ms'.
      finish; try eassumption.
Qed.
End S.
