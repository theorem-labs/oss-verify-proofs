(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv InitMem.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Common Require Import StrFun STRW_tac Startup_kit.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import UImg F_memset F_memcpy Startup_A.
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.
(* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Notation rsegs := UImg.usegs.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rmemsetZ_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A n c : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(A, A + n)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' A [CB (Z.to_nat n) (repeat (Z_to_bv 8 c) (Z.to_nat n))].

Lemma rmemset_specZ : forall (A n c : Z) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (junk : list byte),
  rw_cells rsegs m A [CB (Z.to_nat n) junk] ->
  mem_inv rsegs m ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 c -> a2 = Z_to_bv 64 n ->
  (0 <= c < 256)%Z -> (0 <= n < 2^64)%Z -> (A < 2^64)%Z ->
  evt rsegs (rmemsetZ_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A n c m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1b640) fc None m (seg_rom rsegs)).
Proof.
  intros until junk. intros DST MI -> -> -> Hc Hn Hl.
  pose proof (rw_cells_bound _ _ _ _ DST) as B. cbn [cells_size csize Nat.add] in B.
  Local Ltac2 Set LiaHints.tbl := fun () => "0040>28807598860.413748405345.43 55345754776.4361929834785.4200000600<00B00HS2Hl1BS2Hc1BS2Hc1BS2Hn1B".
assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; lia).
  assert (En : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  assert (Ec : (bv_unsigned (Z_to_bv 64 c) mod 256 = c)%Z) by (rewrite unsigned_lit by lia; apply Z.mod_small; lia).
  eapply evt_mono. { eapply memset_spec; [|exact MI]. rewrite EA, En. exact DST. }
  intros ms' PO. unfold memset_post in PO. rewrite EA, En, Ec in PO. exact PO.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Definition rmemcpyZ_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A S n : Z) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(A, A + n)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' A [CB (Z.to_nat n) src]
    /\ bytes_at rsegs m' S src.

Lemma rmemcpy_specZ : forall (A S n : Z) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (src junk : list byte),
  bytes_at rsegs m S src ->
  length src = Z.to_nat n ->
  rw_cells rsegs m A [CB (Z.to_nat n) junk] ->
  (S + n <= A \/ A + n <= S)%Z ->
  mem_inv rsegs m ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 n ->
  (0 <= n < 2^64)%Z -> (A < 2^64)%Z -> (S < 2^64)%Z ->
  evt rsegs (rmemcpyZ_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A S n src m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1b23c) fc None m (seg_rom rsegs)).
Proof.
  intros until junk. intros SRC LEN DST SEP MI -> -> -> Hn HA HS.
  pose proof (rw_cells_bound _ _ _ _ DST) as B. cbn [cells_size csize Nat.add] in B.
  pose proof (bytes_at_bound _ _ _ _ SRC) as B2.
  Local Ltac2 Set LiaHints.tbl := fun () => "0040>28813896508.4661929833015.4863007907991.4964303092213.4700000:00D00O00\S3LEN2HA1BS3LEN2Hn1BS3LEN3SEP1BS3LEN2HS1B2B2".
assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
  assert (En : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  eapply evt_mono. { eapply memcpy_spec; [| | | | exact MI]; rewrite ?EA, ?ES, ?En; [exact SRC | exact LEN | exact DST | lia]. }
  intros ms' PO. unfold memcpy_post in PO. rewrite EA, ES, En in PO. exact PO.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation RGOT_SSP := 0x1ccb8%Z (only parsing).
Notation RGUARD := 0x4e298%Z (only parsing).


(* [comment removed for export] *)
Section LeRoundtrip.
Local Open Scope Z_scope.
#[using="Type"] Lemma testbit_small_high : forall a k, 0 <= a < 2 ^ 8 -> 8 <= k -> Z.testbit a k = false.
Proof.
  intros a k Ha Hk. destruct (Z.eq_dec a 0) as [->|Hnz]; [apply Z.bits_0|].
  Local Ltac2 Set LiaHints.tbl := fun () => "0030=26985714323.537914578842.54714269673.5 00000800<00@S2Ha3HnzS2HaS2Hk".
apply Z.bits_above_log2; [lia|]. apply (Z.lt_le_trans _ 8); [| lia]. apply Z.log2_lt_pow2; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma lor_byte_testbit : forall a r k, 0 <= a < 2 ^ 8 -> 0 <= r -> 0 <= k ->
  Z.testbit (Z.lor a (Z.shiftl r 8)) k = if k <? 8 then Z.testbit a k else Z.testbit r (k - 8).
Proof.
  intros a r k Ha Hr Hk. Local Ltac2 Set LiaHints.tbl := fun () => "0040=29856961236.74709649405.7 49457837536.751794599906.600000300600:00>S1lS1nS2HaS2Hk".
rewrite Z.lor_spec, Z.shiftl_spec by lia.
  destruct (Z.ltb_spec0 k 8).
  - rewrite (Z.testbit_neg_r r (k - 8)) by lia. apply orb_false_r.
  - rewrite (testbit_small_high a k) by lia. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma lor_byte_low : forall (b : byte) r, 0 <= r -> Z_to_bv 8 (Z.lor (bv_unsigned b) (Z.shiftl r 8)) = b.
Proof.
  intros b r Hr. pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb.
  apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2 ^ 8).
  apply Z.bits_inj'. intros k Hk.
  destruct (Z.ltb_spec0 k 8).
  - Local Ltac2 Set LiaHints.tbl := fun () => "0070=15378305750.715378338772.735050870977.74709649405.7 51797286755.75360623360.7 53768309194.700000400800;00A00E00I00OS2HbS2HbS1lS2Hb1nS2HkS2HrS2Hb1n".
rewrite Z.mod_pow2_bits_low by lia. rewrite lor_byte_testbit by lia.
    replace (k <? 8) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  - rewrite Z.mod_pow2_bits_high by lia. rewrite (testbit_small_high (bv_unsigned b) k) by lia. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma lor_byte_high : forall a r, 0 <= a < 2 ^ 8 -> 0 <= r -> Z.shiftr (Z.lor a (Z.shiftl r 8)) 8 = r.
Proof.
  intros a r Ha Hr. apply Z.bits_inj'. intros k Hk.
  Local Ltac2 Set LiaHints.tbl := fun () => "0060=14731162487.619520207253.649451054179.650917064737.651794599906.65367504769.6 00000100500900=00A00ESS2HkS2HaS2HkS2HkS2Hr".
rewrite Z.shiftr_spec by lia. rewrite lor_byte_testbit by lia.
  replace (k + 8 <? 8) with false by (symmetry; apply Z.ltb_ge; lia). f_equal. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma bytes_le_to_Z_nonneg : forall bs : list byte, 0 <= bytes_le_to_Z bs.
Proof.
  Local Ltac2 Set LiaHints.tbl := fun () => "0010=39280637297.0000001S".
induction bs as [|b bs IH]; cbn [bytes_le_to_Z]; [lia|].
  apply Z.lor_nonneg. split; [apply bv_unsigned_in_range|]. apply Z.shiftl_nonneg. exact IH.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma Z_to_le_bytes_bytes_le_to_Z : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bytes_le_to_Z_nonneg bs) as Hr. pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb.
  rewrite lor_byte_low by exact Hr. rewrite lor_byte_high by lia. rewrite IH. reflexivity.
Qed.

#[using="Type"] Lemma bytes_le_to_Z_bound : forall bs : list byte, bytes_le_to_Z bs < 2 ^ (8 * Z.of_nat (length bs)).
Proof.
  intros bs.
  pose proof (bytes_le_to_Z_to_le_bytes (length bs) (bytes_le_to_Z bs) (bytes_le_to_Z_nonneg bs)) as E.
  rewrite Z_to_le_bytes_bytes_le_to_Z in E. rewrite E at 1.
  apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
Qed.

#[using="Type"] Lemma le8_le_bytes_to_word : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs L. unfold le8, word_to_le_bytes, le_bytes_to_word.
  pose proof (bytes_le_to_Z_bound bs) as B. rewrite L in B. pose proof (bytes_le_to_Z_nonneg bs) as N.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. Local Ltac2 Set LiaHints.tbl := fun () => "0010<1667379864.4000007S1L1B1N".
rewrite Z.mod_small by (cbn in B |- *; lia).
  rewrite <- L. apply Z_to_le_bytes_bytes_le_to_Z.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End LeRoundtrip.

(* [comment removed for export] *)
Definition canary_bytes (cr : word) : list byte := firstn 1 (le8 cr) ++ [Z_to_bv 8 0] ++ skipn 2 (le8 cr).
Definition canary_of (cr : word) : word := le_bytes_to_word (canary_bytes cr).
Lemma canary_bytes_length : forall cr, length (canary_bytes cr) = 8%nat.
Proof. intros cr. unfold canary_bytes. rewrite !length_app, length_firstn, length_skipn, length_le8. reflexivity. Qed.
Lemma canary_recast_bytes : forall cr,
  cells_bytes [C8 (canary_of cr)] = cells_bytes [CB 1 (firstn 1 (le8 cr)); C1 (Z_to_bv 8 0); CB 6 (skipn 2 (le8 cr))].
Proof.
  intros cr. cbn [cells_bytes cbytes app]. unfold canary_of. rewrite le8_le_bytes_to_word by apply canary_bytes_length.
  unfold canary_bytes. rewrite !app_nil_r, <- ?app_assoc. reflexivity.
Qed.

Definition rinit_ssp_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo R : Z) (cr : word) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x10 x11 : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp (Z_to_bv 64 RTP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (RGUARD, 0x4e2a0); (0x2e020, 0x2e028)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' RGUARD [C8 (canary_of cr)]
    /\ rw_cells rsegs m' RGOT_SSP [C8 (Z_to_bv 64 RGUARD)]
    /\ rw_cells rsegs m' RTD (rtd_cells x0 x1 x2 x3 x4 x5 x6 x7 x8 (canary_of cr) x10 x11)
    /\ bytes_at rsegs m' R (le8 cr).

Lemma rinit_ssp_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo R : Z) (cr : word) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x10 x11 : word) (junk : list byte),
  stk rsegs m lo (bv_unsigned sp) ->
  bytes_at rsegs m R (le8 cr) ->
  rw_cells rsegs m RGUARD [CB 8 junk] ->
  rw_cells rsegs m RGOT_SSP [C8 (Z_to_bv 64 RGUARD)] ->
  rw_cells rsegs m RTD (td_cells x0 x1 x2 x3 x4 x5 x6 x7 x8 x10 x11) ->
  mem_inv rsegs m ->
  tp = Z_to_bv 64 RTP -> a0 = Z_to_bv 64 R ->
  (lo <= bv_unsigned sp - 16)%Z -> (0x4f000 <= lo)%Z -> (bv_unsigned sp <= R)%Z ->
  evt rsegs (rinit_ssp_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo R cr x0 x1 x2 x3 x4 x5 x6 x7 x8 x10 x11 m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x142e8) fc None m (seg_rom rsegs)).
Proof.
  intros until junk. intros ST RND GU GG TDC MI -> -> LO LOLO SPR.
  unfold td_cells in TDC.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (RGUARD, 0x4e2a0); (0x2e020, 0x2e028)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bytes_at_bound _ _ _ _ RND) as RB. rewrite length_le8 in RB.
  Local Ltac2 Set LiaHints.tbl := fun () => "00Z0>13731562011.8915768085431.8216787763480.7219872837808.8920433961190.6225656252822.7826505308628.7226505308628.8926505308628.9326796773613.8827027239232.9329553121821.8729823858968.7230487722008.7231399144472.7632031302765.8232614775744.703832226837.77 42337895669.8242390975095.6343059315771.6043428190325.825038834024.72 50819712397.6351725834733.9252122355040.8952217171120.9352232676784.8954164510851.6954164510851.8454245763789.9155323567583.645588681619.63 5705618843.93 58697251573.8259314923118.6463191641311.8264806981808.9365212743211.7167081926311.697702271666.81 8605882000.63 00000<00L00X00Y00]00a00e00i00m00n01>01?01K01W01[01g01n02502902=02D02H02P02T02U02e02f02g02k02o03003403D03P03Q03c03d03e03m04104:04>S2LO4LOLO2RBS2LO4LOLO3SPR2RBS2LO4LOLO2RBSS2RBS2RBS2RBS2RBS2RBSS2LO4LOLO3SPR2RBSS2LO4LOLO2RBS2LO4LOLO2RBS2RBS2LO4LOLO2RBS2RB2HBS2LO2RBS2RBS2RBS2LO2RBS2RBS3SPR2RBS2RBSS2LO4LOLO3SPR2RBSSS2RBS2RBSS2RBS2LO4LOLO3SPR2RBS2LO4LOLO2RBFS2LO4LOLO3SPR2RB1KFSS3RSP2RBS2RBS4LOLO2RBS2RB".
carve_frame 16%nat ST.
  lstep. lstep. lstep. if_cases K; zify_cond K; [exfalso; lia|]. clear K.
  do 4 lstep.
  lstep. call (rmemcpy_specZ RGUARD R 8); [exact RND | rewrite length_le8; reflexivity | exact GU | lia | exact MI | reflexivity | reflexivity | reflexivity | lia | lia | lia |].
  rename PC into GU. clear RND. rename POST into RND. change (Z.to_nat 8) with 8%nat in GU. try rename MI0 into MI.
  lstep. lstep. lstep. lstep.
  (* [comment removed for export] *)
  apply (rw_cells_recast rsegs _ _ _ [C8 (canary_of cr)]) in GU;
    [| cbn; repeat split; exact I | apply canary_recast_bytes | reflexivity].
  lstep. lstep. lstep.
  do 2 lstep. release_frame FR ST (bv_unsigned sp). lstep.
  unfold rinit_ssp_post, rtd_cells. sys_finish.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
Definition pauxv20 (hw uid rnd : word) : list word :=
  [Z_to_bv 64 3; Z_to_bv 64 0x10040; Z_to_bv 64 4; Z_to_bv 64 56; Z_to_bv 64 5; Z_to_bv 64 10; Z_to_bv 64 16; hw;
   Z_to_bv 64 6; Z_to_bv 64 4096; Z_to_bv 64 11; uid; Z_to_bv 64 12; uid; Z_to_bv 64 23; z64;
   Z_to_bv 64 25; rnd; z64; z64].

Notation RENVIRON := 0x2df60%Z (only parsing).
Notation RPROGNAME := 0x4e2a8%Z (only parsing).   (* [comment removed for export] *)
Notation RHWCAP := 0x4e320%Z (only parsing).
Notation RGOT3 := 0x1cc90%Z (only parsing).       (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma renvp_count_loop : forall (ws : list word) (Q : machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (A : Z) (rest : list byte),
  Forall (fun w : word => bv_unsigned w <> 0%Z) ws ->
  bytes_at rsegs m A (u64s ws ++ le8 z64 ++ rest) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (A + 8 * (Z.of_nat (length ws) + 1))) z64 a1 a2 a3 a4 a5
                    a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x13a04) fc None m (seg_rom rsegs)) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5
                    a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x139f8) fc None m (seg_rom rsegs)).
Proof.
  induction ws as [|w ws IH]; intros until rest; intros NZ B HQ.
  - cbn [u64s app] in B.
    pose proof (bytes_at_bound _ _ _ _ B) as BB. rewrite app_length, length_le8 in BB.
    pose proof (rd_u64 rsegs m A z64 rest (Z_to_bv 64 A) B eq_refl) as RD.
    zstep. clear RD. zstep. zstep.
    cbn [length Z.of_nat] in HQ. exact_evt HQ.
  - cbn [u64s app] in B. rewrite <- app_assoc in B.
    pose proof (bytes_at_bound _ _ _ _ B) as BB. rewrite !app_length, !length_le8 in BB.
    apply Forall_cons_iff in NZ. destruct NZ as [NZw NZ].
    pose proof (rd_u64 rsegs m A w _ (Z_to_bv 64 A) B eq_refl) as RD.
    zstep. clear RD. zstep. zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0090>17811497213.4421476511129.4422638646069.4423191505603.4427474062459.4429479961955.4438004400391.4456582425032.4460905788144.4400000800<00=00>00?00@00A00B00CS3NZw2BBS2BBFFFFFFF".
if_true.
    apply bytes_at_app in B. destruct B as [_ B]. rewrite length_le8 in B.
    eapply (IH Q); [exact NZ | exact B |].
    cbn [length] in HQ. exact_evt HQ.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".





Section RInitLibc.
  Variables (ra sp gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
            (E : Z) (eps : list word) (R : Z) (P : Z) (s : list byte)
            (pn0 pnf0 hw0 env0 uid hw cr : word) (gjunk : list byte).
  Notation W := [(bv_unsigned sp - 448, bv_unsigned sp); (RENVIRON, 0x2df68); (RTD, 0x2e0b8); (0x4e040, 0x4e070);
                 (RGUARD, 0x4e2a0); (RPROGNAME, 0x4e2b8); (RLIBC, 0x4e328)]%Z.
  Notation AUXV := (E + 8 * (Z.of_nat (length eps) + 1))%Z.

  Definition rinit_libc_post : Z -> machine_state -> Prop :=
    fun t ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' pg m',
    ms' = MS (mkR ra sp gp (Z_to_bv 64 RTP) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch W m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' RTD (rtd_cells (Z_to_bv 64 RTD) (Z_to_bv 64 RTD) (Z_to_bv 64 RTD) z64 (Z_to_bv 64 t) z64 (Z_to_bv 64 2)
                                (Z_to_bv 64 0x2dfe0) (Z_to_bv 64 0x4e2f0) (canary_of cr) (Z_to_bv 64 0x2e040) z64)
    /\ rw_cells rsegs m' RLIBC (libc_cells (Z_to_bv 8 1) (Z_to_bv 64 AUXV) (Z_to_bv 64 224) (Z_to_bv 64 8) (Z_to_bv 64 4096))
    /\ rw_cells rsegs m' RTLL [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 (Z_to_bv 64 8); C8 z64]
    /\ rw_cells rsegs m' RSYSINFO [C8 z64]
    /\ rw_cells rsegs m' RPROGNAME [C8 pg; C8 (Z_to_bv 64 P)]
    /\ rw_cells rsegs m' RHWCAP [C8 hw]
    /\ rw_cells rsegs m' RENVIRON [C8 (Z_to_bv 64 E)]
    /\ rw_cells rsegs m' RDEFSTACK [C4 (Z_to_bv 64 0x20000)]
    /\ rw_cells rsegs m' RGUARD [C8 (canary_of cr)]
    /\ rw_cells rsegs m' RGOT3 [C8 (Z_to_bv 64 RENVIRON); C8 (Z_to_bv 64 0x4e2b0); C8 (Z_to_bv 64 RPROGNAME)]
    /\ rw_cells rsegs m' RGOT_SSP [C8 (Z_to_bv 64 RGUARD)]
    /\ rw_cells rsegs m' RGOT_DYNAMIC [C8 z64]
    /\ bytes_at rsegs m' E (u64s eps ++ le8 z64 ++ u64s (pauxv20 hw uid (Z_to_bv 64 R)))
    /\ bytes_at rsegs m' P (s ++ [Z_to_bv 8 0])
    /\ bytes_at rsegs m' R (le8 cr)
    /\ (0 < t < 4194304)%Z.

  Hypothesis EPS : Forall (fun w : word => bv_unsigned w <> 0%Z) eps.
  Hypothesis NONUL : Forall (fun b : byte => bv_unsigned b <> 0%Z) s.
  Hypothesis LO : (lo <= bv_unsigned sp - 448)%Z.
  Hypothesis LOLO : (0x4f000 <= lo)%Z.
  Hypothesis SPE : (bv_unsigned sp <= E)%Z.
  Hypothesis SPP : (bv_unsigned sp <= P)%Z.
  Hypothesis SPR : (bv_unsigned sp <= R)%Z.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition rpn_post (x5 x6 x7 x9 x11 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m0 : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists pg m',
    ms' = MS (mkR (Z_to_bv 64 0x139ec) (Z_to_bv 64 (bv_unsigned sp + -384)) gp x11 (* [comment removed for export] *) x5 x6 x7
                  (Z_to_bv 64 P) x9 (Z_to_bv 64 RPROGNAME) (Z_to_bv 64 (P + Z.of_nat (length s) + 1)) (Z_to_bv 64 47) z64 x14 x15 x16 x17
                  (Z_to_bv 64 RLIBC) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
             F (Z_to_bv 64 0x13ac8) fc None m' (seg_rom rsegs)
    /\ munch [(RPROGNAME, 0x4e2b0)]%Z m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' RPROGNAME [C8 pg; C8 (Z_to_bv 64 P)].

  #[using="lo NONUL LO LOLO SPP"] Lemma rpn_loop : forall (k : nat) (j : Z) (m0 mm : word -> option byte) x5 x6 x7 x9 x11 x13 x14 x15 x16 x17 x28 x29 x30 x31 pg,
    (Z.of_nat k = Z.of_nat (length s) + 1 - j)%Z -> (1 <= j)%Z ->
    munch [(RPROGNAME, 0x4e2b0)]%Z m0 mm -> wmono rsegs m0 mm -> mem_inv rsegs mm ->
    bytes_at rsegs mm P (s ++ [Z_to_bv 8 0]) ->
    rw_cells rsegs mm RPROGNAME [C8 pg; C8 (Z_to_bv 64 P)] ->
    evt rsegs (rpn_post x5 x6 x7 x9 x11 x14 x15 x16 x17 x28 x29 x30 x31 m0)
      (MS (mkR (Z_to_bv 64 0x139ec) (Z_to_bv 64 (bv_unsigned sp + -384)) gp x11 x5 x6 x7
               (Z_to_bv 64 P) x9 (Z_to_bv 64 RPROGNAME) (Z_to_bv 64 (P + j)) (Z_to_bv 64 47) x13 x14 x15 x16 x17
               (Z_to_bv 64 RLIBC) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x13abc) fc None mm (seg_rom rsegs)).
  Proof.
    induction k as [|k IH]; intros j m0 mm x5 x6 x7 x9 x11 x13 x14 x15 x16 x17 x28 x29 x30 x31 pg Hk Hj MU WM MI STR G2.
    - pose proof (bytes_at_bound _ _ _ _ STR) as BB. rewrite app_length in BB. cbn [length] in BB.
      assert (Hn : nth_error (s ++ [Z_to_bv 8 0]) (Z.to_nat (j - 1)) = Some (Z_to_bv 8 0)).
      { Local Ltac2 Set LiaHints.tbl := fun () => "00D0?11798819898.79 11798917686.85 15909455332.10221262278978.87 21262475328.86 27695076341.85 27695502841.79 29784362992.78 33300089623.10247938600305.10053671475478.81 57438790759.82 58268345609.10158340751337.86 58340816619.87 59160449310.78 59308628179.87 66786336327.79 7060371760.86  7060568114.87  00000700>00Q00X00_00i01301:01A01H01U01_01f02002:02A02R02Y02`02gS2Hk2BBS2Hk2BBS2LO4LOLO3SPP2Hk2BBS2Hk2BBS2Hk2BBS2Hk2Hj2BBS2Hk2Hj2BBS2Hk2BBS2Hk2BBS2Hk2BBS2Hk2Hj2BB2HbS2Hk2Hj2BBS2Hk2BBS2Hk2Hj2BBS2Hk2Hj2BBS2Hk2BBS2Hk2BB3NZb2Rb2K0S2Hk2BBS2Hk2BBS2Hk2BB".
rewrite nth_error_app2 by lia. replace (Z.to_nat (j - 1) - length s)%nat with 0%nat by lia. reflexivity. }
      pose proof (u8ro_read rsegs mm P _ (j - 1) _ (Z_to_bv 64 (P + j + -1)) STR Hn ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
      zstep. clear RD. zstep. if_false. zstep. if_false.
      replace (Z_to_bv 64 (P + j)) with (Z_to_bv 64 (P + Z.of_nat (length s) + 1)) by (f_equal; lia).
      unfold rpn_post. finish2. all: eassumption.
    - pose proof (bytes_at_bound _ _ _ _ STR) as BB. rewrite app_length in BB. cbn [length] in BB.
      destruct (nth_error s (Z.to_nat (j - 1))) as [b|] eqn:Hb; [| apply nth_error_None in Hb; lia].
      assert (Hn : nth_error (s ++ [Z_to_bv 8 0]) (Z.to_nat (j - 1)) = Some b) by (rewrite nth_error_app1 by lia; exact Hb).
      pose proof (proj1 (Forall_forall _ _) NONUL b (nth_error_In _ _ Hb)) as NZb. cbn in NZb.
      pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. cbn in Rb.
      pose proof (u8ro_read rsegs mm P _ (j - 1) _ (Z_to_bv 64 (P + j + -1)) STR Hn ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
      zstep. clear RD. zstep. if_cases K.
      + (* [comment removed for export] *) lstep. zstep.
        replace (P + j + 1)%Z with (P + (j + 1))%Z by lia.
        eapply (IH (j + 1)%Z); try OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast; lia.
      + zstep. if_cases K0; zify_cond K0; [| exfalso; lia]. zstep.
        replace (P + j + 1)%Z with (P + (j + 1))%Z by lia.
        eapply (IH (j + 1)%Z); try OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast; lia.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  Ltac rscan_it AUXB vi ki :=
    lstep; if_false; ldaux AUXB vi; lstep; lstep;
    (try lazymatch goal with |- context [Z_to_bv 64 (bv_unsigned ?spv + -336 + ?c)] =>
      let off := eval vm_compute in (-336 + c)%Z in
      replace (Z_to_bv 64 (bv_unsigned spv + -336 + c)) with (Z_to_bv 64 (bv_unsigned spv + off)) by (f_equal; lia)
    end);
    (try lazymatch goal with |- context [Z_to_bv 64 (?c + (bv_unsigned ?spv + -336))] =>
      let off := eval vm_compute in (c + -336)%Z in
      replace (Z_to_bv 64 (c + (bv_unsigned spv + -336))) with (Z_to_bv 64 (bv_unsigned spv + off)) by (f_equal; lia)
    end);
    lstep; lstep; ldaux AUXB ki; lstep; astep.

  #[using="EPS NONUL LO LOLO SPE SPP SPR"] Lemma rinit_libc_spec : forall tp a0 a1,
    stk rsegs m lo (bv_unsigned sp) ->
    bytes_at rsegs m E (u64s eps ++ le8 z64 ++ u64s (pauxv20 hw uid (Z_to_bv 64 R))) ->
    bytes_at rsegs m P (s ++ [Z_to_bv 8 0]) ->
    bytes_at rsegs m R (le8 cr) ->
    rw_cells rsegs m RPROGNAME [C8 pn0; C8 pnf0] ->
    rw_cells rsegs m RHWCAP [C8 hw0] ->
    rw_cells rsegs m RENVIRON [C8 env0] ->
    rw_cells rsegs m RSYSINFO [C8 z64] ->
    rw_cells rsegs m RLIBC (libc_cells (Z_to_bv 8 0) z64 z64 z64 z64) ->
    rw_cells rsegs m RTD (td_cells z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 z64) ->
    rw_cells rsegs m RTLL [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64] ->
    rw_cells rsegs m RDEFSTACK [C4 (Z_to_bv 64 0x20000)] ->
    rw_cells rsegs m RGUARD [CB 8 gjunk] ->
    rw_cells rsegs m RGOT3 [C8 (Z_to_bv 64 RENVIRON); C8 (Z_to_bv 64 0x4e2b0); C8 (Z_to_bv 64 RPROGNAME)] ->
    rw_cells rsegs m RGOT_SSP [C8 (Z_to_bv 64 RGUARD)] ->
    rw_cells rsegs m RGOT_DYNAMIC [C8 z64] ->
    mem_inv rsegs m ->
    a0 = Z_to_bv 64 E -> a1 = Z_to_bv 64 P ->
    impl rsegs (at_node rsegs) (enode NSetTid dec_set_tid) (epost rinit_libc_post)
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x139c0) fc None m (seg_rom rsegs)).
  Proof.
    intros tp a0 a1 ST ENV STR RND G2 HW ENVC SI LC TDC MT DS GU GOT3 GG GD MI -> ->.
    unfold td_cells, libc_cells in *.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (bytes_at_bound _ _ _ _ ENV) as EB. rewrite !app_length, !u64s_length, length_le8 in EB. cbn [length pauxv20] in EB.
    pose proof (bytes_at_bound _ _ _ _ STR) as PB. rewrite app_length in PB. cbn [length] in PB.
    pose proof (bytes_at_bound _ _ _ _ RND) as RB. rewrite length_le8 in RB.
    pose proof (bv_unsigned_in_range 64 hw) as RHW. unfold bv_modulus in RHW. cbn in RHW.
    iprefix.
    Local Ltac2 Set LiaHints.tbl := fun () => "08;0?10105082325.10110208488344.11110224280728.11110263306008.11110372821272.89 10527136152.11110781987992.11111008877432.10811362458803.11111675239759.98 11682669592.92 11801586693.10011801586693.101121790400.87   12269999424.10912298875324.12612300972440.1431249923264.109 12504938904.91 1262809904.111 12651403312.11312750448152.89 12907775768.14312907775768.14412909872956.12613193745512.11113212603559.86 1350713240.111 13546642840.1111370291707.102 13826042264.14413828139452.12713854270580.11313860718744.91 13874018840.89 14030163992.11114103120280.89 14319927663.11214454549720.97 14492967044.12714495064224.14414690937624.11114773770875.10214929451771.10214953389193.11115033461680.10815184727320.11115251232024.89 15280898200.11115443323312.1081547406488.111 15615826072.91 15909455332.11116072759534.11116119225496.11116152514676.11216193897880.11116263209368.91 16363512728.91 16428635528.10116520135420.11216547368728.11116633187649.82 16639843451.10216664064016.11216678659567.1111694482328.111 16955585843.11117401321648.11117412536240.10817729606651.10217879908760.91 17969708312.11118226129944.11118287420096.10918358111363.14418582367152.1081874461176.113 18772639256.97 18787962216.1111890133742.89  19042827563.1101924540071.108 19292988396.11319437848984.1111950060339.111 19756625539.10819837149718.12720167022061.10720283889176.11120342994200.11120433046808.11120480040536.97 20559402115.14521106919960.11121210051999.97 21248565009.12521250035837.10021261141756.11321427110040.91 21446616587.12121606717294.91 21798634688.10921798708335.11222164508788.11222282192675.14222568521383.10822586485352.89 22632813821.10022827798576.11323032157684.11123048321211.10223048321211.10323106651666.10323449815576.92 23771026438.82 23848967814.1382394506136.91  24276645784.11124433407655.1082461626747.103 24956574232.11125114623920.10825156273717.14425278459952.11325348372528.11325397459608.11125435258127.14525439460376.11125566553219.14625624113075.11125686175815.97 26052436647.89 26291562981.12426293660097.14226313435160.11126504917904.14326504917904.14426507015092.12626507015092.12726569673582.11126657501232.11326944926836.11327173326324.11127255593243.11327313692824.91 27363063576.1112745835288.111 27630903216.10827716611864.11127992412312.91 28072922155.11028202990515.1112823128243.111 28311219736.92 28630498355.11128678763907.10728678763907.10828769735976.97 28828584216.11128896172952.11129060980891.10829142842027.11029223778381.11129277335577.13529286260248.11129493672240.11229600498485.14329624125464.1112988220916.111 29921765764.11130030441192.91 30113096552.11130453207704.91 31069451160.11131161366443.11031275665304.91 31391753240.11131538458392.11132003221912.91 32183709059.14732267453428.11132476927476.1113268291439.112 32874208973.10632985609624.11133071914371.10533071914371.10833124399503.10133128458032.11133196668075.90 33201983598.11133203292788.11333274356563.10333306564912.11233420355695.11333456576432.10833476328216.92 33746313648.10833766019203.12733791941424.11234084440809.82 341110192.111  34368356123.1133439545240.143 3441642428.126 34441536116.11234488801560.11134581657368.11134700863492.11334839166896.10835069247384.11135601434136.92 35950024308.11335969698112.10236194455448.11136443029364.13336508968579.10836531490629.10036573021083.10836673729405.1003667520560.113 36676273587.11137184280558.11137434831357.10037584867949.11237649347900.12637651445016.14337706291736.11137745848728.11137765068541.10037801431320.11137850036212.11137926564379.1133796882036.113 38541588376.11138670834840.11138806986883.14438867725720.11138880710680.11138887106620.12638889203736.14339031949104.1123916100656.113 39218477360.11239228754616.97 39362511527.10839486458520.11139545589787.11239667454515.11140597677735.88 40662066968.11141135974684.82 4137234328.111 41449156831.97 41514867736.11141568944003.88 41621998744.11141728831143.10842026542952.92 42096762392.11142115915892.11242149033285.10042152937187.12142226762667.90 4249728691.111 42648081816.11142805740039.12442830473904.11142911584408.11142986742680.91 43061412128.77 43210580403.11143372080960.10943461381985.13443538978428.11143608255400.97 43753472635.10243909623960.11143918709876.11344156402712.11144327256216.91 44484923210.10044632929078.10444632929078.12544772910196.11344844277891.14544929527064.11144947645428.11145141649432.11145164892824.91 45349545448.11145451282427.10245499316968.11145589664024.14245589664024.14445591761212.12445592168088.1114594349684.112 4611197235.111 46171365016.11146188222184.11146386664472.1114663504694.107 47064843187.11147389319888.11347625222555.10847938600305.10948201294431.1004829765424.112 48558570734.11148656680829.10048658098328.91 48986915965.10049009737496.11149070646040.11149227803251.97 49594798872.11149663609880.11149688423079.10849704035864.92 49848632626.14149872280128.10849986883736.91 50033228952.11150257303987.11150369698045.10050492928536.11150517196392.11150519191576.11150610110851.10850614273563.11250626392856.11150658621095.10850779300468.11250807790352.11350917177240.11150946885453.1105097758616.111 51112656259.88 51206416239.11351308032497.11051394459580.12651396556696.14251396556696.1445154469992.111 51581833880.92 51829021369.1215186885424.112 51899082816.10951922947120.11152151318827.11052421600432.11152486394484.11252577538839.10852577538839.11152577538839.11252577538839.11352577538839.89 52577538839.91 52577538839.92 5261752856.89  52666173483.91 52670008600.11152745639448.89 52957439655.10853003761688.1115307791860.111 53318030488.11153353928472.11153539719872.11353543943304.97 54105288300.11154118232600.11154147306027.11054259462936.91 54315287064.11154423868352.10955060957918.10055104759171.14655201966568.91 55238157483.11055318278260.11255339957599.10055763832948.11255810242966.96 55876010121.11256213453616.1125626728431.111 56449481859.10856560431343.11156599488848.10856676144116.11156704518544.10856821392576.90 56915657273.10156953734787.10856962556577.10357016027216.82 57109141272.11157353709208.11157449475067.10257621932155.10257769718147.10857916503488.10958224880536.91 58268345609.11058405575860.10358431211800.14358431211800.14458433308988.12558433308988.12658437426542.11158443336216.11158502103832.92 58579945240.11158663588852.11158678274968.91 58760734574.11158807992600.13359017892196.11259164061051.10259233223150.11159314923118.98 59526463513.13659558111536.11259910292248.92 60014780020.11260066885144.89 60368760863.10060501326872.11160577606376.97 6070019700.113 6140783936.89  61422000108.11261664598183.88 61673534251.1106169531118.111 61696300843.88 61933947312.10862139361215.12762141458331.14462162270152.97 62187512707.14762275100015.11362386236669.10062428434736.11262656774424.11162783051928.11162840648256.89 62903315480.11162942489648.11362966227695.10063014573208.11163134267440.11363274684945.12663620716339.11163695263000.89 63738689456.11163850113816.92 63951760515.86 63952241472.10963988606068.11364172722328.11164732787352.11165115206040.11165391197294.91 6555659200.112 65582638196.1136567051160.111 6569749869.111 66063824536.11166106701208.11166118714776.11166215846707.11166338680302.92 66356731416.89 66715894808.11166779399524.11366798234931.11166987871464.1116705158808.111 67135074182.14467137171362.12767289856456.97 67455461400.11167568245808.11367644366360.11167981895704.11168375318195.11168400596251.11268524148688.112694041788.126  6941457560.111 696138904.144  7358632216.111 7381600893.100 763416049.111  7697034008.89  7735147175.108 7922197976.138 8055353624.111 8330899097.137 8460265368.111 847511683.108  8519295128.91  8577286936.92  8603416747.110 8617536816.111 8649037976.143 8651135164.127 8973405208.91  9044833560.89  9064876952.91  9247388440.92  9388565891.105 945228006.79   9569375860.113 9667984280.111 9728861315.89  9855713917.100 9941432856.111 9962270737.127 00000>00L00^01001B01T01f02<02F02P02b02l03603C03P03f04<04I04[04i05305E05[06106G06U06_07107C07M07c07d07n08@08R08d09209D09E09_0:90:K0:U0:_0:i0;30;E0;W0;i0<30<A0<S0<i0=70=I0=S0=e0>70>I0>W0>m0??0?M0?W0?m0@?0@Q0@[0@i0A30A=0AO0Aa0B30B@0BJ0BT0Bj0Bk0C90CG0CU0C_0D50DG0DQ0D[0De0Do0EA0ES0Ee0Ef0F00FB0FC0FY0Fk0GA0GS0Ga0Go0H<0HN0HX0HY0Hc0I10IC0IM0IW0Ii0J?0JU0Jg0K10K;0KM0K_0Ki0Kj0L<0LF0L\0Lf0M00MB0ML0M^0Mh0N20N<0NF0NG0NH0NZ0O00OJ0O`0P:0PH0PR0P\0Pf0Q80QJ0Q\0Qn0R80RJ0R\0Rj0S40S>0SP0SZ0Sd0Sn0So0TA0TS0Te0U30U=0UG0UY0Uc0V90VK0VU0Vk0W90WG0WY0Wk0X90XK0X]0Xo0YA0YK0YU0Y_0Z10Z;0ZM0ZW0Za0Zo0[=0[K0[Y0[c0\90\C0\U0\_0]10];0]E0]O0]Y0]g0^90^:0^P0^Z0^l0_>0_T0_^0`00`B0`L0`[0`i0`j0a40a>0aP0ab0al0b60bD0bV0b`0c60cL0cZ0cl0d>0dP0dZ0dl0e60eH0eZ0ed0f60fH0f^0g40g>0gH0gR0gS0g]0go0hA0hK0hU0hc0hm0i?0iI0iW0ia0j30j=0jK0j]0jg0k60kE0kS0k]0ko0l00l>0lP0lb0lo0m90mF0mS0mi0n30n=0nO0nY0nk0o=0oG0o_10710A10K10]10g11911K11Y11c12112G12]13313E13O13Y13k14914K14c14m15C15U15_15m16716E16W16i17;17M17_17i18;18M18W18i19319I19[19m1:71:I1:[1:i1;71;A1;S1;e1;o1<91<O1<a1<k1==1=G1=Y1=c1>91>O1>e1?31?A1?N1?X1?e1@31@A1@O1@Y1@c1@m1A71AA1AK1AU1A_1B11B?1BQ1Bc1Bm1C?1CI1C[1Cm1DC1DD1DZ1Dl1E:1EH1EZ1Eg1F11F;1FI1FW1Fa1Fk1G51G?1GI1GS1Ge1Go1HA1HW1Ha1I71ID1IE1IO1Ie1Io1JA1JS1J]1Jg1K11K>1KP1KZ1K[1L11L21L31LI1LW1Li1M;1MM1MW1Mi1N71NA1NW1Na1No1OG1OQ1O[1Om1P71PI1PV1Ph1Pi1Q31Q@1QV1Q`1Qn1R<1RJ1RT1Rn1SH1SI1SS1Se1T71TA1TS1Te1U21UD1UN1UO1Ua1Uk1VA1VK1V]1Vk1W=1WG1WT1W^1X01XB1XT1Xb1Y81YB1YT1Y^1Yl1Z:1ZL1ZV1Zd1[61[H1[^1[h1\61\H1\b1]<1]=1]O1]Y1]k1^=1^G1^Y1^o1_01_B1_X1_j1`<1`F1`X1`b1`l1a>1aH1aZ1ad1b61bH1bV1bd1c:1cP1c^1d01dB1dT1d^1dh1e21eD1eN1e`1f21fHS3SPP2EB2PB2RBS3SPP2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO3SPE2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS2EB2PB2RB2HBS2EB2PB2RB2HBS2LO4LOLO2EB2PB2RB3HspS2LO4LOLO2EB2PB2RB3HspS2EB2PB2RB2HBS2LO4LOLO2EB2PB2RBS3SPE2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RB3HspS2LO4LOLO2EB2PB2RB3HspS2LO4LOLO2EB2PB2RB3HspS3SPR2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RB3HspFS2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RBS3SPP2EB2PB2RBS2LO4LOLO2EB2PB2RBFS2LO4LOLO3SPP2EB2PB2RB3HspS2LO4LOLO3SPP2EB2PB2RB3HspS2LO4LOLO2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RBS2EB2PB2RBS3SPP2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO3SPP2EB2PB2RBS3SPE2EB2PB2RBS2LO4LOLO2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RBS3SPE2EB2PB2RBS2LO4LOLO3SPR2EB2PB2RBS2LO4LOLO2EB2PB2RBS3RSP2EB2PB2RBS2EB2PB2RBS2LO4LOLO3SPE2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RBS2EB2PB2RBS3SPE2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RBS2EB2PB2RB2HBS2EB2PB2RBS2EB2PB2RBS2LO4LOLO3SPE2EB2PB2RBFS3SPR2EB2PB2RBS3SPE2EB2PB2RBS3RSP2EB2PB2RBS2EB2PB2RBS2LO4LOLO3SPE2EB2PB2RBS2LO4LOLO2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RBFS2EB2PB2RBS2LO4LOLO2EB2PB2RBFS2LO4LOLO2EB2PB2RB3HspS2LO4LOLO2EB2PB2RBS2LO4LOLO3SPR2EB2PB2RBS2LO4LOLO2EB2PB2RBS3SPR2EB2PB2RBS3SPE2EB2PB2RBS2EB2PB2RB2HBS2LO4LOLO2EB2PB2RBS2EB2PB2RBFS2EB2PB2RBS3SPR2EB2PB2RBS2LO4LOLO2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO3SPE2EB2PB2RBS2LO4LOLO3SPE2EB2PB2RBS2LO4LOLO2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RBS2EB2PB2RBFS2LO4LOLO2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RB3HspS2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS2EB2PB2RBFFS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RB3HspS2LO4LOLO3SPE2EB2PB2RB3HspS2LO4LOLO2EB2PB2RB3HspS2LO4LOLO3SPE2EB2PB2RB3HspS3SPE2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RBS3RSP2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS2EB2PB2RBFS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RBS3RSP2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RB3HspS2LO4LOLO2EB2PB2RBS2EB2PB2RBS2LO4LOLO3SPE2EB2PB2RBS3SPR2EB2PB2RBS3SPR2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RBS3RSP2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS3SPR2EB2PB2RBS3SPE2EB2PB2RBS3RSP2EB2PB2RBS3SPE2EB2PB2RBS2EB2PB2RBS2LO4LOLO3SPP2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS3SPE2EB2PB2RBS2LO4LOLO2EB2PB2RBFS2LO4LOLO2EB2PB2RB3HspS2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO3SPE2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RBS2EB2PB2RBS4LOLO2EB2PB2RBS3SPP2EB2PB2RBFS2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS3SPE2EB2PB2RBS2LO4LOLO2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RB3HspS2LO4LOLO2EB2PB2RB3HspS3SPP2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RB3HspS2LO4LOLO2EB2PB2RB3HspS2EB2PB2RBS2EB2PB2RBS2EB2PB2RBFS2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS3SPP2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RBS2EB2PB2RBS3SPP2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RBS2EB2PB2RBS3SPR2EB2PB2RBS2LO4LOLO2EB2PB2RBS2EB2PB2RBS4LOLO2EB2PB2RBS4LOLO2EB2PB2RBS3RSP2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RBFS3SPE2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO2EB2PB2RBS2EB2PB2RBS2EB2PB2RB2HBS2LO2EB2PB2RBS2LO4LOLO3SPR2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RBS2EB2PB2RBS2LO4LOLO3RSP2EB2PB2RB1HS2LO4LOLO3RSP2EB2PB2RB1HS2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RBS3SPR2EB2PB2RBS2EB2PB2RBS3SPR2EB2PB2RBS2LO4LOLO2EB2PB2RB3HspS2LO4LOLO2EB2PB2RB3HspS2LO4LOLO2EB2PB2RB3HspS2LO4LOLO2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RBS3SPR2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO3RSP2EB2PB2RB1HS2EB2PB2RBS2LO4LOLO3SPP2EB2PB2RBS2LO4LOLO2EB2PB2RBS2EB2PB2RBS3RSP2EB2PB2RBS2EB2PB2RBS3SPE2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RBS2EB2PB2RBS2LO4LOLO3SPR2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RBS3SPR2EB2PB2RBS3SPP2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS2LO4LOLO3SPE2EB2PB2RBS2LO4LOLO2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RB3HspS2LO4LOLO2EB2PB2RB3HspS2LO4LOLO2EB2PB2RB3HspS3SPR2EB2PB2RBS3SPP2EB2PB2RBS2LO2EB2PB2RBS2EB2PB2RBS2EB2PB2RB2HBS3SPE2EB2PB2RBS3RSP2EB2PB2RBS3SPE2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RBS3RSP2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO3SPR2EB2PB2RBFS2LO4LOLO3SPE2EB2PB2RBS2LO4LOLO2EB2PB2RBS3RSP2EB2PB2RBS3SPP2EB2PB2RBS2LO4LOLO2EB2PB2RBS2EB2PB2RB2HBS2EB2PB2RBS2EB2PB2RBS3SPR2EB2PB2RBS3RSP2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO3SPP2EB2PB2RBS2EB2PB2RBS2LO4LOLO3SPE2EB2PB2RBS2EB2PB2RB2HBFS2EB2PB2RBS2LO4LOLO3SPR2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS2EB2PB2RB2HBS2LO4LOLO2EB2PB2RBS2EB2PB2RBFS2LO4LOLO2EB2PB2RB3HspFFS2LO4LOLO2EB2PB2RB3HspS3SPE2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RBS3SPE2EB2PB2RBS2EB2PB2RBS2LO4LOLO3SPP2EB2PB2RBS2EB2PB2RBS3SPE2EB2PB2RBS2LO4LOLO3SPP2EB2PB2RB1KS2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO2EB2PB2RBS2LO4LOLO2EB2PB2RBFS2EB2PB2RBS2EB2PB2RB2HBS2LO4LOLO3SPE2EB2PB2RBS2EB2PB2RBS3RSP2EB2PB2RBS3SPE2EB2PB2RBS3RSP2EB2PB2RBS2EB2PB2RBS2LO4LOLO3SPE2EB2PB2RB3HspS2LO4LOLO3SPE2EB2PB2RB3HspFS2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RBS2EB2PB2RB2HBS2LO4LOLO2EB2PB2RBS2EB2PB2RBFS2LO4LOLO2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RB3HspS2EB2PB2RBS2LO4LOLO2EB2PB2RBS3SPE2EB2PB2RBS2LO4LOLO2EB2PB2RBS2EB2PB2RBS2EB2PB2RB2HBS2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RBS3SPE2EB2PB2RBS2LO4LOLO3SPR2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RBS2EB2PB2RBS3SPP2EB2PB2RBS3SPP2EB2PB2RBS2LO4LOLO2EB2PB2RBS2EB2PB2RBS3SPE2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO3SPP2EB2PB2RBS2EB2PB2RBS3SPR2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO3SPR2EB2PB2RB3HspS2LO4LOLO3SPR2EB2PB2RB3HspFS2LO4LOLO2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO3SPP2EB2PB2RBFS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RB3HspS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RBS3RSP2EB2PB2RBS3SPE2EB2PB2RBS2LO4LOLO2EB2PB2RB3HspS2LO4LOLO2EB2PB2RB3HspS3SPP2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RBS2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RBS2LO4LOLO2EB2PB2RB3Hsp".
carve_frame 384%nat ST.
    do 10 lstep.
    (* [comment removed for export] *)
    apply (rw_cells_split_CB rsegs _ _ [] 352 _ _ [48; 304]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
    apply (proj1 (rw_cells_app _ _ _ [_] _)) in FR. destruct FR as [FRlo FR]. cbn [cells_size csize Nat.add] in FR.
    apply (proj1 (rw_cells_app _ _ _ [_] _)) in FR. destruct FR as [AUX FRhi]. cbn [cells_size csize Nat.add] in FRhi.
    change (Z.of_nat 48) with 48%Z in *. change (Z.of_nat 304) with 304%Z in *.
    replace (bv_unsigned sp + -384 + 48)%Z with (bv_unsigned sp + -336)%Z in AUX by lia.
    replace (bv_unsigned sp + -384 + 48 + 304)%Z with (bv_unsigned sp + -32)%Z in FRhi by lia.
    lstep. call (rmemset_specZ (bv_unsigned sp + -336) 304 0); [exact AUX | exact MI | reflexivity | reflexivity | reflexivity | lia | lia | lia |].
    rename POST into AUX. change (Z.to_nat 304) with 304%nat in AUX. try rename MI0 into MI.
    apply (rw_cells_recast rsegs _ _ _ (repeat (C8 z64) 38)) in AUX;
      [| cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity]. cbn [repeat] in AUX.
    (* [comment removed for export] *)
    lstep. lstep. lstep.
    eapply (renvp_count_loop eps); [exact EPS | exact ENV |].
    (* [comment removed for export] *)
    lstep. lstep. lstep.
    pose proof ENV as AUXB. apply bytes_at_app in AUXB. destruct AUXB as [_ AUXB].
    apply bytes_at_app in AUXB. destruct AUXB as [_ AUXB]. rewrite u64s_length, length_le8 in AUXB.
    replace (E + Z.of_nat (8 * length eps) + Z.of_nat 8)%Z with AUXV in AUXB by lia.
    ldaux AUXB 0%nat. lstep. if_false. lstep. lstep. lstep. lstep.
    (* [comment removed for export] *)
    rscan_it AUXB 1%nat 2%nat. rscan_it AUXB 3%nat 4%nat. rscan_it AUXB 5%nat 6%nat. rscan_it AUXB 7%nat 8%nat.
    rscan_it AUXB 9%nat 10%nat. rscan_it AUXB 11%nat 12%nat. rscan_it AUXB 13%nat 14%nat. rscan_it AUXB 15%nat 16%nat.
    rscan_it AUXB 17%nat 18%nat.
    (* [comment removed for export] *)
    steps_to 0x13a7c%Z.
    astep. if_cases K; zify_cond K; [|exfalso; lia]. clear K.
    astep. if_cases K; zify_cond K; [|exfalso; lia]. clear K.
    (* [comment removed for export] *)
    steps_to 0x13abc%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      call (rpn_loop (length s) 1 mm mm); [lia | lia | apply munch_refl | apply wmono_refl | exact MI | exact STR | exact G2 | ] end.
    rename POST into G2. try rename MI0 into MI.
    (* [comment removed for export] *)
    apply (proj1 (rw_cells_app _ _ _ [_;_;_] _)) in AUX. destruct AUX as [AUXa AUX].
    apply (proj1 (rw_cells_app _ _ _ [_;_;_] _)) in AUX. destruct AUX as [AUX3 AUXb].
    cbn [cells_size csize Nat.add] in AUX3, AUXb. change (Z.of_nat 24) with 24%Z in *.
    replace (bv_unsigned sp + -336 + 24)%Z with (bv_unsigned sp + -312)%Z in AUX3 by lia.
    replace (bv_unsigned sp + -336 + 24 + 24)%Z with (bv_unsigned sp + -288)%Z in AUXb by lia.
    lstep. lstep.
    name_sp sp (-384)%Z. name_sp sp (-336)%Z.
    icallk (rinit_tls_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
               lo z64 (Z_to_bv 64 4096) (Z_to_bv 64 AUXV)).
    all: lazymatch goal with
         | |- forall _, _ => ipost rsegs; unname_sp; unname_sp
         | |- _ => unname_sp; unname_sp;
                   first [ hyp_by_addr | reflexivity | lia
                         | lazymatch goal with |- rw_cells _ _ (?b + -336 + 24)%Z _ =>
                             replace (b + -336 + 24)%Z with (b + -312)%Z by lia; hyp_by_addr end ]
         end.
    rename PC into ST. unfold td_cells, libc_cells in *.
    (* [comment removed for export] *)
    lstep. lstep.
    call_sp (rinit_ssp_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo R cr).
    all: lazymatch goal with
         | |- evt _ _ _ => idtac
         | |- ?g => first [ hyp_by_addr | reflexivity | lia ]
         end.
    match goal with H : stk _ _ _ _ |- _ => rename H into ST end.
    (* [comment removed for export] *)
    do 3 lstep. if_false. lstep. lstep. lstep. if_false. lstep. lstep. if_true.
    do 5 lstep.
    join2 FRlo AUXa. join2 FRlo AUX3. join2 FRlo AUXb. join2 FRlo FRhi.
    release_frame FRlo ST (bv_unsigned sp).
    lstep.
    unfold rinit_libc_post, td_cells, rtd_cells, libc_cells in *. sys_finish; try lia.
    all: hyp_by_addr.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End RInitLibc.

