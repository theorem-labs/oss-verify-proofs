(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv InitMem.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import StrFun STRW_tac Startup_kit.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImgX F_memset F_memcpy Startup_A.
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Notation rsegs := UImg.usegs.
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
F (Z_to_bv 64 0x1c534) fc None m (seg_rom rsegs)).
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
F (Z_to_bv 64 0x1c130) fc None m (seg_rom rsegs)).
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
Notation RGOT_SSP := 0x1dbb0%Z (only parsing).
Notation RGUARD := 0x4f1a0%Z (only parsing).
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
/\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (RGUARD, 0x4f1a8); (0x2ef20, 0x2ef28)]%Z m m'
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
(lo <= bv_unsigned sp - 16)%Z -> (0x50000 <= lo)%Z -> (bv_unsigned sp <= R)%Z ->
evt rsegs (rinit_ssp_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo R cr x0 x1 x2 x3 x4 x5 x6 x7 x8 x10 x11 m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x15108) fc None m (seg_rom rsegs)).
Proof.
intros until junk. intros ST RND GU GG TDC MI -> -> LO LOLO SPR.
unfold td_cells in TDC.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (RGUARD, 0x4f1a8); (0x2ef20, 0x2ef28)]%Z m) as MU.
pose proof (wmono_refl rsegs m) as WM.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
pose proof (bytes_at_bound _ _ _ _ RND) as RB. rewrite length_le8 in RB.
Local Ltac2 Set LiaHints.tbl := fun () => "00>0>17910556051.6320433961190.6231399144472.763832226837.77 43059315771.6050819712397.6354164510851.6954164510851.8455323567583.645613357462.78 59314923118.6467081926311.696972738039.63 8605882000.63 00000@00D00H00O00V00Z00^00b00f00j01<01@01D01HS2LO4LOLO3SPR2RBS2RBS2RBS2LO2RBS2LO2RBS2RBS2RBS2RBS2RBS2RBS2LO4LOLO3SPR2RB1KS2RBS2RBS2RB".
carve_frame 16%nat ST.
lstep. lstep. lstep. if_cases K; zify_cond K; [exfalso; lia|]. clear K.
do 4 lstep.
lstep. call (rmemcpy_specZ RGUARD R 8); [exact RND | rewrite length_le8; reflexivity | exact GU | lia | exact MI | reflexivity | reflexivity | reflexivity | lia | lia | lia |].
rename PC into GU. clear RND. rename POST into RND. change (Z.to_nat 8) with 8%nat in GU. try rename MI0 into MI.
lstep. lstep. lstep. lstep.
apply (rw_cells_recast rsegs _ _ _ [C8 (canary_of cr)]) in GU;
[| cbn; repeat split; exact I | apply canary_recast_bytes | reflexivity].
lstep. lstep. lstep.
do 2 lstep. release_frame FR ST (bv_unsigned sp). lstep.
unfold rinit_ssp_post, rtd_cells. sys_finish.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition pauxv20 (hw uid rnd : word) : list word :=
[Z_to_bv 64 3; Z_to_bv 64 0x10040; Z_to_bv 64 4; Z_to_bv 64 56; Z_to_bv 64 5; Z_to_bv 64 10; Z_to_bv 64 16; hw;
Z_to_bv 64 6; Z_to_bv 64 4096; Z_to_bv 64 11; uid; Z_to_bv 64 12; uid; Z_to_bv 64 23; z64;
Z_to_bv 64 25; rnd; z64; z64].
Notation RENVIRON := 0x2ee60%Z (only parsing).
Notation RPROGNAME := 0x4f1b0%Z (only parsing).
Notation RHWCAP := 0x4f228%Z (only parsing).
Notation RGOT3 := 0x1db88%Z (only parsing).
Lemma renvp_count_loop : forall (ws : list word) (Q : machine_state -> Prop)
ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (A : Z) (rest : list byte),
Forall (fun w : word => bv_unsigned w <> 0%Z) ws ->
bytes_at rsegs m A (u64s ws ++ le8 z64 ++ rest) ->
evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (A + 8 * (Z.of_nat (length ws) + 1))) z64 a1 a2 a3 a4 a5
a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x14790) fc None m (seg_rom rsegs)) ->
evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5
a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x14784) fc None m (seg_rom rsegs)).
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
zstep. clear RD. zstep. zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0090>17811497213.4421476511129.4422638646069.4423191505603.4427474062459.4429479961955.4436008218864.4438004400391.4456582425032.4400000800<00=00>00?00@00A00B00CS3NZw2BBS2BBFFFFFFF".
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
Notation W := [(bv_unsigned sp - 448, bv_unsigned sp); (RENVIRON, 0x2ee68); (0x2ee68, 0x2efb8); (0x4ef40, 0x4ef70);
(RGUARD, 0x4f1a8); (RPROGNAME, 0x4f1c0); (RLIBC, 0x4f230)]%Z.
Notation AUXV := (E + 8 * (Z.of_nat (length eps) + 1))%Z.
Definition rinit_libc_post : Z -> machine_state -> Prop :=
fun t ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' pg m',
ms' = MS (mkR ra sp gp (Z_to_bv 64 RTP) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch W m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' RTD (rtd_cells (Z_to_bv 64 RTD) (Z_to_bv 64 RTD) (Z_to_bv 64 RTD) z64 (Z_to_bv 64 t) z64 (Z_to_bv 64 2)
(Z_to_bv 64 0x2eee0) (Z_to_bv 64 0x4f1f8) (canary_of cr) (Z_to_bv 64 0x2ef40) z64)
/\ rw_cells rsegs m' RLIBC (libc_cells (Z_to_bv 8 1) (Z_to_bv 64 AUXV) (Z_to_bv 64 224) (Z_to_bv 64 8) (Z_to_bv 64 4096))
/\ rw_cells rsegs m' RTLL [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 (Z_to_bv 64 8); C8 z64]
/\ rw_cells rsegs m' RSYSINFO [C8 z64]
/\ rw_cells rsegs m' RPROGNAME [C8 pg; C8 (Z_to_bv 64 P)]
/\ rw_cells rsegs m' RHWCAP [C8 hw]
/\ rw_cells rsegs m' RENVIRON [C8 (Z_to_bv 64 E)]
/\ rw_cells rsegs m' RDEFSTACK [C4 (Z_to_bv 64 0x20000)]
/\ rw_cells rsegs m' RGUARD [C8 (canary_of cr)]
/\ rw_cells rsegs m' RGOT3 [C8 (Z_to_bv 64 RENVIRON); C8 (Z_to_bv 64 0x4f1b8); C8 (Z_to_bv 64 RPROGNAME)]
/\ rw_cells rsegs m' RGOT_SSP [C8 (Z_to_bv 64 RGUARD)]
/\ rw_cells rsegs m' RGOT_DYNAMIC [C8 z64]
/\ bytes_at rsegs m' E (u64s eps ++ le8 z64 ++ u64s (pauxv20 hw uid (Z_to_bv 64 R)))
/\ bytes_at rsegs m' P (s ++ [Z_to_bv 8 0])
/\ bytes_at rsegs m' R (le8 cr)
/\ (0 < t < 4194304)%Z.
Hypothesis EPS : Forall (fun w : word => bv_unsigned w <> 0%Z) eps.
Hypothesis NONUL : Forall (fun b : byte => bv_unsigned b <> 0%Z) s.
Hypothesis LO : (lo <= bv_unsigned sp - 448)%Z.
Hypothesis LOLO : (0x50000 <= lo)%Z.
Hypothesis SPE : (bv_unsigned sp <= E)%Z.
Hypothesis SPP : (bv_unsigned sp <= P)%Z.
Hypothesis SPR : (bv_unsigned sp <= R)%Z.
Definition rpn_post (x5 x6 x7 x9 x11 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m0 : word -> option byte) : machine_state -> Prop :=
fun ms' => exists pg m',
ms' = MS (mkR (Z_to_bv 64 0x14778) (Z_to_bv 64 (bv_unsigned sp + -384)) gp x11 x5 x6 x7
(Z_to_bv 64 P) x9 (Z_to_bv 64 RPROGNAME) (Z_to_bv 64 (P + Z.of_nat (length s) + 1)) (Z_to_bv 64 47) z64 x14 x15 x16 x17
(Z_to_bv 64 RLIBC) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0x14854) fc None m' (seg_rom rsegs)
/\ munch [(RPROGNAME, 0x4f1b8)]%Z m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m'
/\ rw_cells rsegs m' RPROGNAME [C8 pg; C8 (Z_to_bv 64 P)].
#[using="lo NONUL LO LOLO SPP"] Lemma rpn_loop : forall (k : nat) (j : Z) (m0 mm : word -> option byte) x5 x6 x7 x9 x11 x13 x14 x15 x16 x17 x28 x29 x30 x31 pg,
(Z.of_nat k = Z.of_nat (length s) + 1 - j)%Z -> (1 <= j)%Z ->
munch [(RPROGNAME, 0x4f1b8)]%Z m0 mm -> wmono rsegs m0 mm -> mem_inv rsegs mm ->
bytes_at rsegs mm P (s ++ [Z_to_bv 8 0]) ->
rw_cells rsegs mm RPROGNAME [C8 pg; C8 (Z_to_bv 64 P)] ->
evt rsegs (rpn_post x5 x6 x7 x9 x11 x14 x15 x16 x17 x28 x29 x30 x31 m0)
(MS (mkR (Z_to_bv 64 0x14778) (Z_to_bv 64 (bv_unsigned sp + -384)) gp x11 x5 x6 x7
(Z_to_bv 64 P) x9 (Z_to_bv 64 RPROGNAME) (Z_to_bv 64 (P + j)) (Z_to_bv 64 47) x13 x14 x15 x16 x17
(Z_to_bv 64 RLIBC) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0x14848) fc None mm (seg_rom rsegs)).
Proof.
induction k as [|k IH]; intros j m0 mm x5 x6 x7 x9 x11 x13 x14 x15 x16 x17 x28 x29 x30 x31 pg Hk Hj MU WM MI STR G2.
- pose proof (bytes_at_bound _ _ _ _ STR) as BB. rewrite app_length in BB. cbn [length] in BB.
assert (Hn : nth_error (s ++ [Z_to_bv 8 0]) (Z.to_nat (j - 1)) = Some (Z_to_bv 8 0)).
{ Local Ltac2 Set LiaHints.tbl := fun () => "00@0>11798819898.7911798917686.8521262278978.8721262475328.8622089940822.8127695076341.8527695502841.7929784362992.7857438790759.8258340751337.8658340816619.8759160449310.7859308628179.8766786336327.797060371760.86 7060568114.87 00000700>00E00L00Y00c00m01401>01H01R01Y01j02102802?S2Hk2BBS2Hk2BBS2Hk2BBS2Hk2BBS2Hk2Hj2BB2HbS2Hk2Hj2BBS2Hk2Hj2BBS2Hk2BBS2Hk2Hj2BBS2Hk2Hj2BBS2Hk2Hj2BBS2Hk2BBS2Hk2BB3NZb2Rb2K0S2Hk2BBS2Hk2BBS2Hk2BB".
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
+ lstep. zstep.
replace (P + j + 1)%Z with (P + (j + 1))%Z by lia.
eapply (IH (j + 1)%Z); try eassumption; lia.
+ zstep. if_cases K0; zify_cond K0; [| exfalso; lia]. zstep.
replace (P + j + 1)%Z with (P + (j + 1))%Z by lia.
eapply (IH (j + 1)%Z); try eassumption; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
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
rw_cells rsegs m RGOT3 [C8 (Z_to_bv 64 RENVIRON); C8 (Z_to_bv 64 0x4f1b8); C8 (Z_to_bv 64 RPROGNAME)] ->
rw_cells rsegs m RGOT_SSP [C8 (Z_to_bv 64 RGUARD)] ->
rw_cells rsegs m RGOT_DYNAMIC [C8 z64] ->
mem_inv rsegs m ->
a0 = Z_to_bv 64 E -> a1 = Z_to_bv 64 P ->
impl rsegs (at_node rsegs) (enode NSetTid dec_set_tid) (epost rinit_libc_post)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x1474c) fc None m (seg_rom rsegs)).
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
Local Ltac2 Set LiaHints.tbl := fun () => "01F0?11675239759.98 13212603559.86 14454549720.97 16633187649.82 18358111363.14418772639256.97 1924540071.108 19756625539.10820480040536.97 20559402115.14521210051999.97 21446616587.12121596792820.13322568521383.10823771026438.82 23848967814.13824433407655.10825435258127.14525566553219.14625686175815.97 26052436647.89 28678763907.10728678763907.10828769735976.97 29277335577.13532183709059.14733071914371.10533071914371.10833766019203.12734084440809.82 36508968579.10836531490629.10038806986883.14439228754616.97 39362511527.10840597677735.88 41135974684.82 41449156831.97 41568944003.88 41728831143.10842149033285.10042152937187.12143061412128.77 43461381985.13443608255400.97 44632929078.10444632929078.12544844277891.14545364753430.96 4663504694.107 48201294431.10049227803251.97 49688423079.10850610110851.10850658621095.10851112656259.88 51829021369.12152957439655.10853543943304.97 55060957918.10055104759171.14655339957599.10056449481859.10856953734787.10857016027216.82 57769718147.10858807992600.13359314923118.98 59526463513.13660368760863.10060577606376.97 61664598183.88 61964145074.14162162270152.97 62187512707.14762966227695.10063951760515.86 67289856456.97 68037708182.1277735147175.108 7922197976.138 8330899097.137 847511683.108  9388565891.105 945228006.79   9728861315.89  00000:00D00E00S00]00^00h01201301=01>01L01M01W01a01b01l02602@02J02T02^02h02i03303=03G03Q03[03\03f04004:04;04E04O04Y04c04m05705F05U05b05o06006H06`06j06k07C07Q07[07e07o08908C08P08Z08[08e08o09909C09M09N09X09b0::0:D0:Q0:R0:\0:f0:g0;10;20;<0;=0;>0;H0;R0;\0;f0<00<:0<DS2EB2PB2RBS2EB2PB2RBFS3RSP2EB2PB2RBS2EB2PB2RBFS2EB2PB2RBS2EB2PB2RBFS2EB2PB2RBFS3SPR2EB2PB2RBFS2EB2PB2RBS2EB2PB2RBSS2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS2EB2PB2RBFS2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS2EB2PB2RBSS2EB2PB2RBS2EB2PB2RBS2EB2PB2RBFS2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS4LOLO2EB2PB2RBS4LOLO2EB2PB2RBS2LO2EB2PB2RBS2LO2EB2PB2RBSS2LO4LOLO3RSP2EB2PB2RB1HS2LO4LOLO3RSP2EB2PB2RB1HS2EB2PB2RBSS2LO4LOLO3RSP2EB2PB2RB1HS3RSP2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS2LO2EB2PB2RBS2EB2PB2RBFS2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS2EB2PB2RBSS2EB2PB2RBS2EB2PB2RBS2LO4LOLO3SPP2EB2PB2RB1KS2EB2PB2RBS2LO2EB2PB2RBFS2EB2PB2RBS2EB2PB2RBFS2EB2PB2RBFS2EB2PB2RBFSS2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS2EB2PB2RBS2EB2PB2RB".
carve_frame 384%nat ST.
do 10 lstep.
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
lstep. lstep. lstep.
eapply (renvp_count_loop eps); [exact EPS | exact ENV |].
lstep. lstep. lstep.
pose proof ENV as AUXB. apply bytes_at_app in AUXB. destruct AUXB as [_ AUXB].
apply bytes_at_app in AUXB. destruct AUXB as [_ AUXB]. rewrite u64s_length, length_le8 in AUXB.
replace (E + Z.of_nat (8 * length eps) + Z.of_nat 8)%Z with AUXV in AUXB by lia.
ldaux AUXB 0%nat. lstep. if_false. lstep. lstep. lstep. lstep.
rscan_it AUXB 1%nat 2%nat. rscan_it AUXB 3%nat 4%nat. rscan_it AUXB 5%nat 6%nat. rscan_it AUXB 7%nat 8%nat.
rscan_it AUXB 9%nat 10%nat. rscan_it AUXB 11%nat 12%nat. rscan_it AUXB 13%nat 14%nat. rscan_it AUXB 15%nat 16%nat.
rscan_it AUXB 17%nat 18%nat.
steps_to 0x14808%Z.
astep. if_cases K; zify_cond K; [|exfalso; lia]. clear K.
astep. if_cases K; zify_cond K; [|exfalso; lia]. clear K.
steps_to 0x14848%Z.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
call (rpn_loop (length s) 1 mm mm); [lia | lia | apply munch_refl | apply wmono_refl | exact MI | exact STR | exact G2 | ] end.
rename POST into G2. try rename MI0 into MI.
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
lstep. lstep.
call_sp (rinit_ssp_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo R cr).
all: lazymatch goal with
| |- evt _ _ _ => idtac
| |- ?g => first [ hyp_by_addr | reflexivity | lia ]
end.
match goal with H : stk _ _ _ _ |- _ => rename H into ST end.
do 3 lstep. if_false. lstep. lstep. lstep. if_false. lstep. lstep. if_true.
do 5 lstep.
join2 FRlo AUXa. join2 FRlo AUX3. join2 FRlo AUXb. join2 FRlo FRhi.
release_frame FRlo ST (bv_unsigned sp).
lstep.
unfold rinit_libc_post, td_cells, rtd_cells, libc_cells in *. sys_finish; try lia.
all: hyp_by_addr.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End RInitLibc.
