(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import StrFun.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import ZBridge.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg ABase AKit ShadowTac ADepot_iface ADepot ADepotKit.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes_k12.
(* [comment removed for export] *)

Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Section CANSEC1. Context {rc : runConstT}.
Definition imemcpy_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(t0 t1 t2 a0 a5 a6 a7 t3 t4 t5 t6 : word) (D : Z) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists a1 a2 a3 a4 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom bsegs)
/\ munch [(D, D + Z.of_nat (length src))]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ rw_cells bsegs m' D [CB (length src) src].
Section Memcpy.
Variables (RNG : footprint)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S : Z) (src rest junk : list byte).
Notation D := (bv_unsigned a0).
Notation n := (Z.of_nat (length src)).
Hypothesis MI : mem_inv bsegs m.
Hypothesis SRC : bytes_at bsegs m S (src ++ rest).
Hypothesis DST : rw_cells bsegs m D [CB (length src) junk].
Hypothesis A1 : a1 = Z_to_bv 64 S.
Hypothesis A2 : a2 = Z_to_bv 64 n.
Hypothesis SEP : (S + Z.of_nat (length (src ++ rest)) <= D \/ D + n <= S)%Z.
Hypothesis DSMALL : (D + n < 2^63)%Z.
Hypothesis SSMALL : (S + Z.of_nat (length (src ++ rest)) < 2^63)%Z.
Hypothesis RS : rng RNG S n.
Hypothesis RD : rng RNG D n.
Notation POST := (imemcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t0 t1 t2 a0 a5 a6 a7 t3 t4 t5 t6 D src m).
#[using="rest junk SRC DST SEP DSMALL RS RD"] Lemma imemcpy_loop : forall (k : nat) (i : Z) (mc : word -> option byte) (bs : list byte) x14,
Z.to_nat (n - i) = k -> (0 <= i < n)%Z ->
u8arr bsegs mc D bs -> length bs = length src -> (forall j, (j < Z.to_nat i)%nat -> nth_error bs j = nth_error src j) ->
munch [(D, D + n)]%Z m mc -> wmono bsegs m mc -> mem_inv bsegs mc ->
evtF bsegs RNG POST
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (S + i)) (Z_to_bv 64 (D + n)) (Z_to_bv 64 (D + i)) x14 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x64188) fc None mc (seg_rom bsegs)).
Proof.
pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
pose proof (bytes_at_bound _ _ _ _ SRC) as SB. rewrite length_app in SB.
Local Ltac2 Set LiaHints.tbl := fun () => "00F0>10364520306.691129708843.72 13708355367.6915404439176.6915410598582.6915416934737.7016747840457.9 19526850107.7019526868180.7119622189599.6923153198281.733436568184.69 4325898847.69 5120842917.81 57904774905.7257905327519.7259308548577.6759310630224.6459893199455.698611898281.71 8611898281.72 8931259039.69 00000A00X00i01:01M01a01l02=02N02f03703J03X03i04904Q04e05605D05W05o06GS2DB2SB2Hk2Hi3LBSS2DB2SB2Hk2Hi3LBS1K1n1HS2DB2SB2Hk2Hi3LBSS2DB2SB2Hk2Hi3LBSS2DB2SB2Hk2Hi3LBS1KS2DB2SB2Hk2Hi3LBS2HjS3SEP2DB2SBS2DB2SB2Hk2Hi3LBSS2DB2SB2Hk2Hi3LBSS6DSMALL2DB2SB2Hk2Hi3LBSS2DB2SB2Hk2Hi3LBSS2DB2SB2Hk2Hi3LBS1KS2DB2SB2Hk3LBSS2DB2SB2Hk2Hi3LBSS2DB2SB2Hk3LBS1HS2DB2SB2Hk2Hi3LBS1K2Hj1nS2DB2SB2Hk2Hi3LBS2NBS2DB2SB2Hk2Hi3LBSS2DB2SB2Hk3LBSS2DB2SB2Hk2Hi3LBS1nS2DB2SB2Hk2Hi3LBS1K2Hj1nS6DSMALL2DB2SB2Hk2Hi3LBS".
induction k as [|k IH]; intros i mc bs x14 Hk Hi ARR LBS DONE MU WM MI1; [exfalso; lia|].
destruct (nth_error src (Z.to_nat i)) as [b|] eqn:NB. 2:{ exfalso. apply nth_error_None in NB. lia. }
assert (SRC1 : bytes_at bsegs mc S (src ++ rest)).
{ eapply bytes_at_transport; [exact SRC | exact MU |]. cbn [disjoint_from]. clear - SEP Hi SB DB. lia. }
pose proof (u8ro_read bsegs mc S (src ++ rest) i b (wa (S + i)) SRC1 ltac:(rewrite nth_error_app1 by lia; exact NB) ltac:(lia) eq_refl) as RDb.
zstep. cbv beta.
pose proof (u8arr_store_ok bsegs mc D bs i (wa (D + i)) ARR ltac:(rewrite LBS; lia) eq_refl) as SOK.
zstep.
pose proof (u8arr_write bsegs mc D bs i b ARR ltac:(rewrite LBS; lia)) as ARR'.
change (le1 (Z_to_bv 64 (bv_unsigned b))) with (le1 (zxb b)). rewrite le1_zxb.
store_done.
zstep. zstep. zstep. if_cases K; zify_cond K.
- replace (D + i + 1)%Z with (D + (i + 1))%Z by lia. replace (S + i + 1)%Z with (S + (i + 1))%Z by lia.
eapply (IH (i + 1)%Z); [lia | lia | exact ARR' | rewrite Arr.upd_length; exact LBS | | assumption | assumption | assumption].
+ intros j Hj. destruct (Nat.eq_dec j (Z.to_nat i)).
* subst j. rewrite Arr.nth_error_upd_same by (rewrite LBS; lia). symmetry; exact NB.
* rewrite Arr.nth_error_upd_other by lia. apply DONE. lia.
- zstep.
assert (E : upd bs (Z.to_nat i) b = src).
{ apply nth_error_ext. intros j. destruct (Nat.eq_dec j (Z.to_nat i)).
* subst j. rewrite Arr.nth_error_upd_same by (rewrite LBS; lia). symmetry; exact NB.
* rewrite Arr.nth_error_upd_other by lia. destruct (Nat.lt_ge_cases j (Z.to_nat i)); [apply DONE; lia|].
rewrite (proj2 (nth_error_None _ _)) by (rewrite LBS; lia). rewrite (proj2 (nth_error_None _ _)) by lia. reflexivity. }
rewrite E in ARR'. apply rw_cells_of_u8arr in ARR'. finish.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="S rest junk MI SRC DST A1 A2 SEP DSMALL RS RD"] Lemma imemcpy_body : (1 <= n < 2^64)%Z ->
evtF bsegs RNG POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x6417c) fc None m (seg_rom bsegs)).
Proof.
intros N1. pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
pose proof (bytes_at_bound _ _ _ _ SRC) as SB. rewrite length_app in SB.
pose proof (munch_refl [(D, D + n)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM. subst a1 a2.
zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0080>10640767904.5216077671799.5230823899914.5253004074301.5259308646881.5 60134654234.526625077458.52 67943303862.5200000:00D00K00L00U00V00]00gS2N12DB2SBS2N12DB2SBS2DB2SBFS1K2N12DBFS2DB2SBS2N12DB2SB".
if_cases K; zify_cond K. { exfalso. revert K N1 DB. clear. intros K N1 DB. Z.div_mod_to_equations. lia. }
zstep. zstep.
replace a0 with (Z_to_bv 64 (D + 0)) at 3 by (rewrite Z.add_0_r; apply Z_to_bv_bv_unsigned).
replace (Z_to_bv 64 S) with (Z_to_bv 64 (S + 0)) by (f_equal; lia).
eapply (imemcpy_loop (Z.to_nat n) 0 m junk); try assumption; try lia.
- eapply u8arr_of_rw_cells. exact DST.
- pose proof DST as [[WF _] _]. cbn in WF. destruct WF as [WF _]. exact WF.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Memcpy.
Definition imemcpy_postZ (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word) (D : Z) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists a1 a2 a3 a4 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom bsegs)
/\ munch [(D, D + Z.of_nat (length src))]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ rw_cells bsegs m' D [CB (length src) src].
#[using="Type"] Lemma imemcpy_specZ : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (D S n : Z) (src rest junk : list byte),
mem_inv bsegs m -> bytes_at bsegs m S (src ++ rest) -> rw_cells bsegs m D [CB (length src) junk] ->
n = Z.of_nat (length src) ->
(S + Z.of_nat (length (src ++ rest)) <= D \/ D + n <= S)%Z ->
(D + n < 2^63)%Z -> (S + Z.of_nat (length (src ++ rest)) < 2^63)%Z -> (1 <= n)%Z ->
rng RNG S n -> rng RNG D n ->
evtF bsegs RNG (imemcpy_postZ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 D src m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x6417c) fc None m (seg_rom bsegs)).
Proof.
intros until junk. intros MI SRC DST -> SEP DS SS N1 RS RD.
pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
Local Ltac2 Set LiaHints.tbl := fun () => "0020>50463930673.498549018784.48 00000:00DS2DS2N12DBS2DS2N12DB".
assert (U : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
eapply evtF_mono.
{ eapply (imemcpy_body RNG ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) _ a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m S src rest junk);
rewrite ?U; try eassumption; try reflexivity; lia. }
intros ms' P. unfold imemcpy_post in P. rewrite !U in P. exact P.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma amo_add_w_le4 : forall tf cnt, (0 <= tf)%Z -> (0 <= cnt)%Z -> (tf + cnt < 2^32)%Z ->
Z_to_le_bytes 4 (bv_unsigned (amo_val AMO_ADD (bv_extract 0 32 (le_bytes_to_word (le4 (Z_to_bv 64 tf)))) (low32 (Z_to_bv 64 cnt))))
= le4 (Z_to_bv 64 (tf + cnt)).
Proof.
intros tf cnt H0 H1 H2. unfold le4 at 2. Local Ltac2 Set LiaHints.tbl := fun () => "0070=11597642244.811600047760.641352023633.748466830417.754259705740.655033206788.655041854608.600000:00D00N00X00\00f010S2H02H12H2S2H02H12H2S2H02H12H2S2H02H12H2S2H0S2H02H12H2S2H02H12H2".
rewrite unsigned_lit by lia. f_equal.
cbn [amo_val]. rewrite bv_add_unsigned.
assert (E1 : bv_unsigned (bv_extract 0 32 (le_bytes_to_word (le4 (Z_to_bv 64 tf)))) = tf).
{ rewrite bv_extract_unsigned. rewrite le_bytes_to_word_le4. rewrite unsigned_lit by lia.
rewrite Z.shiftr_0_r. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32)%Z with (2^32)%Z. rewrite !Z.mod_small by lia. reflexivity. }
assert (E2 : bv_unsigned (low32 (Z_to_bv 64 cnt)) = cnt).
{ unfold low32. rewrite bv_extract_unsigned. rewrite unsigned_lit by lia. rewrite Z.shiftr_0_r.
unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32)%Z with (2^32)%Z. rewrite Z.mod_small by lia. reflexivity. }
rewrite E1, E2. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32)%Z with (2^32)%Z. rewrite Z.mod_small by lia. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
Ltac amo_stepW4 :=
lazymatch goal with
| |- evtF ?segs ?RNG ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
lazymatch fw with Some ?w =>
let d := eval vm_compute in (decode_any w) in
lazymatch d with Some (?i, ?sz) =>
eapply (evtF_step_acc segs RNG);
[ reflexivity
| rewrite (stepF_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
exec_cbv; amo_decide; exec_cbv; simp_is_x0; simp_regs; vnorm_for i;
try solve_load; try solve_store; reflexivity
| solve_accs
| simp_regs; vnorm_for i; rewrite amo_add_w_le4 by lia; mem_after_store_opt ]
end end
end.
Section CANSEC2. Context {rc : runConstT}.
Section Lock.
Variables (RNG : footprint)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo B v : Z).
Hypothesis MI : mem_inv bsegs m.
Hypothesis ST : stk bsegs m lo (bv_unsigned sp).
Hypothesis LO : (lo <= bv_unsigned sp - 48)%Z.
Hypothesis ALO : (AIMG_HI <= lo)%Z.
Hypothesis A0 : a0 = Z_to_bv 64 B.
Hypothesis CELL : rw_cells bsegs m B [C4 (Z_to_bv 64 v)].
Hypothesis BV : (0 <= v < 2^31)%Z.
Hypothesis BA : (B mod 4 = 0 /\ TAB <= B /\ B + 4 <= NUNIQ)%Z.
Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
Hypothesis RB : rng RNG B 4.
Definition lock_post : machine_state -> Prop :=
fun ms' => exists x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m' lw,
ms' = MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 v) x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (ret_pc ra) fc None m' (seg_rom bsegs)
/\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (B, B + 4)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ stk bsegs m' lo (bv_unsigned sp)
/\ rw_cells bsegs m' B [C4 lw].
#[using="MI ST LO ALO A0 CELL BV BA RSTK RB"] Lemma lock_body : evtF bsegs RNG lock_post
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x734d4) fc None m (seg_rom bsegs)).
Proof.
pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp); (B, B + 4)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption). unfold AIMG_HI, TAB, NUNIQ in *.
Local Ltac2 Set LiaHints.tbl := fun () => "00b0>13172413352.5213624457060.6613624457062.581800609155.61 1800609155.69 24638473347.6124638473347.6727907155492.5929431497298.6729442629968.5729442630097.5529442630230.5931378308326.5331378620384.5832164731367.6032164731367.6537452664998.5437454847525.5640600968423.6040600968426.6841991641667.5742630527489.5543057221392.5143988483203.5943988483203.6745299709328.5545848756903.5949649769127.6251711223320.585187432548.61 5187432548.66 52105090727.6153459164111.6553469114889.5753471300778.5654243526019.6154243526019.665576237813.64 5584011775.57 5586288476.56 59308628304.3 59308628433.2 59308628566.1 59308628695.2 60858483367.6163305555623.6164997134979.6264997134979.6765495973220.6665495973223.6000000400500600700800900:00>00B00I00M00T00U00V00W00X00\00`00a00b00c00g00k00l00m01101201301401501601701801901:01;01<01=01>01?01F01J01N01R01S01T01U01V01W01XS2LOSSSSSSS2LOS2BVS2K22BVS2BVS2BV2K4SSSSS2BVS2BVSSSS2BAS2LOSSS2BASSSSSSSSSSSSSSS2BV2K1S2K2S2K3S2K4SSSSSS".
assert (RSTK' : rng RNG (bv_unsigned sp + -48) 48) by (eapply rng_sub'; [exact RSTK| lia]).
subst a0. carve_frame 48%nat ST.
do 10 zstep. zstep. rewrite sx32_lit by lia.
zstep. if_cases K1; zify_cond K1. 2:{ exfalso. clear - BV K1. lia. }
zstep.
assert (AMO : amo_aligned AW (Z_to_bv 64 B) = true) by (apply amo_alignedW_intro; [lia| lia]).
amo_stepA AMO. rewrite sx32_lit by lia.
zstep. if_cases K2; zify_cond K2. { exfalso. clear -K2. lia. }
amo_stepA AMO.
zstep. if_cases K3; zify_cond K3. { exfalso. clear -K3. cbv in K3. lia. }
zstep. if_cases K4; zify_cond K4. 2:{ exfalso. clear -K4. lia. }
do 7 zstep.
release_frame FR ST (bv_unsigned sp).
apply evtF_done. unfold lock_post.
replace (bv_unsigned sp - 48)%Z with (bv_unsigned sp + -48)%Z by lia.
do 16 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption. all: match goal with H : rw_cells bsegs _ B ?c |- _ => idtac c; exact H end.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Lock.
End CANSEC2.
Ltac shr0 :=
repeat match goal with |- context [Z.shiftr ?x ?k] =>
replace (Z.shiftr x k) with 0%Z by (rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; lia) end.
Section CANSEC3. Context {rc : runConstT}.
Section NStoreFile.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.
Local Ltac solve_load ::= first [ solve_load_guarded | solve_load_image ].
Local Ltac solve_store ::= solve_store_guarded.
Section NStore.
Variables (RNG : footprint)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
(lo NDp AR T sz tf STORE : Z) (HW : word) (tb : list word) (jn jl js jh jf : list byte).
Hypothesis MI : mem_inv bsegs m.
Hypothesis ST : stk bsegs m lo (bv_unsigned sp).
Hypothesis LO : (lo <= bv_unsigned sp - 112)%Z.
Hypothesis ALO : (ATOP <= lo)%Z.
Hypothesis A0 : a0 = Z_to_bv 64 NDp.
Hypothesis A2 : a2 = Z_to_bv 64 AR.
Hypothesis A3 : a3 = HW.
Hypothesis ARGS : rw_cells bsegs m AR [C8 (Z_to_bv 64 T); C4 (Z_to_bv 64 sz); C4 (Z_to_bv 64 0)].
Hypothesis ARB : (bv_unsigned sp <= AR /\ AR + 16 <= 2^47)%Z.
Hypothesis NODE : rw_cells bsegs m NDp [CB 8 jn; CB 4 jl; CB 4 js].
Hypothesis CTF : rw_cells bsegs m SSTF [C8 (Z_to_bv 64 tf)].
Hypothesis CPTR : rw_cells bsegs m SSPTR [C8 (Z_to_bv 64 STORE)].
Hypothesis CST : rw_cells bsegs m SSST [C4 (Z_to_bv 64 tf)].
Hypothesis FRAMES : rw_cells bsegs m (STORE + 8 * tf) [CB 8 jh; CB (Z.to_nat (8 * sz)) jf].
Hypothesis TB : u64arr bsegs m T tb.
Hypothesis LTB : length tb = 255%nat.
Hypothesis SZ : (1 <= sz <= 255)%Z.
Hypothesis TF : (0 <= tf /\ tf + sz + 1 < 1048576)%Z.
Hypothesis TBB : (bv_unsigned sp <= T /\ T + 2040 <= 2^47)%Z.
Hypothesis NDB : (AIMG_HI <= NDp /\ NDp + 16 <= ATOP /\ NDp mod 16 = 0)%Z.
Hypothesis STOB : (AIMG_HI <= STORE /\ STORE + 8388608 <= ATOP /\ STORE mod 4096 = 0)%Z.
Hypothesis SEPNS : (NDp + 16 <= STORE + 8 * tf \/ STORE + 8 * (tf + sz + 1) <= NDp)%Z.
Hypothesis RI : rng_aimg RNG.
Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
Hypothesis RAR : rng RNG AR 16.
Hypothesis RND : rng RNG NDp 16.
Hypothesis RFR : rng RNG (STORE + 8 * tf) (8 * (sz + 1)).
Hypothesis RT : rng RNG T 2040.
Definition nstore_post : machine_state -> Prop :=
fun ms' => exists x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m',
ms' = MS (mkR ra sp gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (ret_pc ra) fc None m' (seg_rom bsegs)
/\ munch [(bv_unsigned sp - 112, bv_unsigned sp); (NDp, NDp + 16); (SSTF, SSTF + 8); (SSST, SSST + 4); (STORE + 8 * tf, STORE + 8 * tf + 8 * (sz + 1))]%Z m m'
/\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ stk bsegs m' lo (bv_unsigned sp)
/\ rw_cells bsegs m' NDp [C8 HW; CB 4 jl; C4 (Z_to_bv 64 (tf + 1))]
/\ rw_cells bsegs m' SSTF [C8 (Z_to_bv 64 (tf + sz + 1))]
/\ rw_cells bsegs m' SSST [C4 (Z_to_bv 64 (tf + sz + 1))]
/\ rw_cells bsegs m' (STORE + 8 * tf) [C8 (Z_to_bv 64 sz); CB (Z.to_nat (8 * sz)) (firstn (Z.to_nat (8 * sz)) (u64s tb))]
/\ rw_cells bsegs m' AR [C8 (Z_to_bv 64 T); C4 (Z_to_bv 64 sz); C4 (Z_to_bv 64 0)].
#[using="rc jn js jh jf MI ST LO ALO A0 A2 A3 ARGS ARB NODE CTF CPTR CST FRAMES TB LTB SZ TF TBB NDB STOB SEPNS RI RSTK RAR RND RFR RT"] Lemma nstore_body : evtF bsegs RNG nstore_post
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x72a58) fc None m (seg_rom bsegs)).
Proof.
pose proof (munch_refl [(bv_unsigned sp + -112, bv_unsigned sp); (NDp, NDp + 16); (SSTF, SSTF + 8); (SSST, SSST + 4); (STORE + 8 * tf, STORE + 8 * tf + 8 * (sz + 1))]%Z m) as MU.
pose proof (wmono_refl bsegs m) as WM.
assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption). unfold AIMG_HI, SSTF, SSPTR, SSST in *.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
Local Ltac2 Set LiaHints.tbl := fun () => "02]0?10411647463.95 10489398501.10211077935948.95 11593749418.10511593749418.92 12587650279.89 12587650282.11413098894204.10413520218209.87 13520218212.95 13520218213.11213520218216.11513520218219.11413620867140.1001508639646.105 15149862570.10515422468449.93 1560509925.100 1560509925.96  1560509931.114 16007310588.10517088274784.10217103458764.93 18045588882.94 18239100277.94 18446219239.11018446219239.91 19338285270.10519338285270.91 19373511525.93 19373511528.11519589112390.10519680783712.11519680783712.93 21028037403.3  21418632967.94 21764122956.11621764122956.89 21764122956.97 21848846242.10221894104544.11521894104544.89 2221946199.102 22364832150.10423122445900.95 23993334155.10123993334155.98 2492914022.95  2492914022.98  2597469155.114 27679091076.83 27780997068.91 28119612256.11528119612256.93 28990961846.94 29032285152.11429032285152.92 29056984305.10229141972172.93 29469427431.96 29469427431.99 29756005259.10229756005259.11429756005259.11629756005259.98 29782367974.10030640719399.95 31688689248.11231688689248.93 31874498834.10132441363056.12633183415099.98 33508037984.11633508037984.91 34290115814.82 34642181227.10234943365921.96 34985880335.10935158841676.94 35835696073.10936960507030.91 37047490023.99 37453426021.11237453426022.90 39939243268.10340373330341.11241169553244.86 41178353612.93 41513302182.10541564619544.10241809465927.85 42957278038.94 43055432124.80 43303441508.92 43303441512.11544021460374.92 44085631722.91 44708047596.93 45015350225.10545236992039.10745667945696.10045667945696.97 46355298535.91 46355298538.11347399595340.97 48237786102.11448475049000.10550633028432.93 51423379376.10551438510464.11452260433120.11752260433120.94 52504176569.10054330877797.11354330877798.87 55034195860.10155034195860.11255034195865.10155034195866.11455034195867.10055036293010.11655770193284.88 55946304394.10256777289882.12657241388115.10558872313774.11459308628304.3  59308628433.1  59308628695.1  59308628820.1  59308629211.1  59314873579.5  59314873579.8  59382398767.10559586081460.11260324194812.10160357415926.98 60511600900.10460698737376.11860698737376.95 60853221185.98 61328998664.11462048608059.10262048608059.98 63401989926.10063401989931.10663404087074.97 63409910945.86 63409911719.89 64267814368.11764267814368.95 64426527463.91 64426527466.11365178518140.10365360148067.11665362245221.93 65504523926.10565510090920.11266077201632.11466077201632.11666077201632.11766077201632.89 66077201632.97 67760998476.92 6818787088.83  7825307013.101 8158244420.90  8796731207.133 8894204422.94  8897956419.105 8935173666.116 8937270820.112 9719060044.89  00000500K00P00i01=01B01L01V01[01`01j02402>02T02U02V02[02`02e02o03H03^03c03h04B04L04Q04[04`04e04o05H05R05W05^05c05m06206706V06`06e07;07E07J07O07T07Y07^07h08008508?08D08X08b08g09O09T09Y09^09c09m0:70:<0:F0:K0:U0:Z0:d0;R0;W0;a0;f0;k0<00<50<:0<?0<D0<X0<l0=60=;0=H0=R0=Z0=_0=`0=j0=o0>40><0>A0>K0>P0>d0>i0?B0?S0?X0?]0?b0?l0@10@;0@H0@V0@c0A00A:0A?0AD0AN0AS0Ag0B@0BT0Bm0CA0CZ0Cb0DA0E90EC0ED0EK0EO0ES0EW0E[0Ed0F00F=0FG0FQ0FV0Fc0Fm0G20GC0GM0GR0GW0G_0Gg0Go0H70H?0HI0HN0HS0H]0Hg0I10I60I@0IJ0IT0I^0Ih0Im0J20J70J?0JX0J]0KQ0KV0Kc0L<0LU0LZS3LTBS3LTB2SZ3NDB4STOB4LSRCS3LTBS3LTB2SZ2TF3NDB4STOB4LSRCS3LTB2SZ2TF3NDB4STOBS3LTBS3LTB4LSRCS3LTB4LSRCS3LTBS3LTBS3LTB4LSRCS3LTB4LSRCS3LTB4LSRCS3LTB2SZ3NDB4STOB4LSRCFFS3LTBS3LTBS3LTBS3LTB4LSRCS3LTB2SZ2TF3NDB4STOB4LSRCS3LTB2SZ3NDB4STOB4LSRCS3LTBS3LTBS3LTB2SZ2TF3NDB4STOB5SEPNSS3LTB4LSRCS3LTBS3LTB4LSRCS3LTBS3LTBS3LTB4LSRCS3LTB2SZ2TF3NDB4STOB4LSRCS3LTB4LSRCS3LTBS2SZ2K3S3LTBS3LTB4LSRCS3LTBS3LTBS3LTB2SZ2TF3TBB3NDB4STOB4LSRC1HS3LTB4LSRCS3LTBS3LTB2SZ3NDB4STOB4LSRCS3LTB4LSRCS3LTBS3LTBS3LTBS3LTBS3LTBS3LTB4LSRCS2LO3LTBS3LTBS3LTB4LSRCS3LTBS3LTB2SZ2TF3NDB4STOBS3LTB4LSRCS3LTBS2LO3ALO3EFA3LTB2SZ2TF3TBB3NDB4STOB4LSRCS3LTBS3LTBS3LTBS3LTBS3LTB4LSRCS3LTB4LSRCS3LTBS3LTB4LSRCS3LTBS3LTB4LSRCS3LTBS3LTB4LSRCS3EFA3LTB2SZ2TF3NDB4STOB2K12K62K74LSRC1H2H02H4S3LTBS3LTB4LSRCS3LTBS3LTBS3LTBS3LTBS3LTBS3LTBS3LTBS3LTB2SZ2TF3NDB4STOBS3LTB2SZ2TF3NDB4STOBS3LTB4LSRCS3LTBS2LO3LTB4LSRCS3LTB4LSRCS3LTB2SZS3LTBFS3LTB4LSRCS3LTBS3LTBS2LO3LTBS3LTBS3LTB4LSRCS3LTBS3LTB2SZ2TF3NDB4STOBS3LTBS3LTB2SZ2TF3NDB4STOB4LSRCS3LTB2SZ3NDB4STOBS3LTBS3LTBS3LTBS3LTB4LSRCS3LTBS3LTB4LSRCS2LO3LTB4LSRCS3LTB3NDB4STOBS3LTB2TF4LSRCS3LTB2TF4LSRCS3LTB4LSRCS3LTBS3LTBS3LTB4LSRCS3LTBS3LTB2SZ2TF3NDB4STOBS3LTB2SZ2TF3NDB4STOB4LSRCS3LTB2SZ2TF3NDB4STOBS3LTB2SZ2TF3NDB4STOB4LSRCS3LTB2SZ2TF3NDB4STOBS3LTB2SZ2TF3NDB4STOB4LSRCS2LO3LTBS3EFA3LTB2SZ2TF3NDB4STOB4LSRC1HS3EFA3LTB2SZ2TF3NDB4STOB5SEPNS2K12K62K74LSRC1H2H02H43H14S3LTB4LSRCFS2SZ2K1S2K2S2K4S2K5S2K8S4STOB2K6S2TF4STOB2K7S3LTB2SZ4LSRCS3LTB4LSRCS3LTB4LSRCS3LTBS2LO3LTB4LSRCS3LTB4LSRCS3LTBS3LTB2SZ3NDB4STOBS3LTB4LSRCS3LTBS3LTBS3LTB2SZS3LTB2SZS3LTB2SZS3LTB2SZS3LTB2SZS3LTB4LSRCS3LTBS3LTBS3LTB4LSRCS3LTB4LSRCS3LTB4LSRCS3LTBS3LTB4LSRCS3LTB4LSRCS3LTB4LSRCS3LTB4LSRCS3LTB4LSRCS3LTBS3LTBS3LTBS2LO3LTBS3LTB2SZ2TF3NDB4STOB4LSRCS3LTBS3EFA3LTB2SZ2TF3NDB4STOB2K12K62K74LSRC1H2H02H42H52H9S3LTBS3LTB2TF4LSRCS3LTB2SZ2TF3NDB4STOB4LSRCS3LTB2SZ2TF3NDB4STOB4LSRCS3LTB".
assert (RSTK' : rng RNG (bv_unsigned sp + -112) 112) by (eapply rng_sub'; [exact RSTK| lia]).
subst a0 a2 a3.
change (?P) with (sf_hide P) in SEPNS.
pose proof FRAMES as FRM. change (?P) with (sf_hide P) in FRAMES. pose proof NODE as NDC. change (?P) with (sf_hide P) in NODE.
pose proof ARGS as ARGC. change (?P) with (sf_hide P) in ARGS.
carve_frame 32%nat ST.
do 10 zstep. zstep.
carve_frame 64%nat ST.
do 9 zstep. zstep. rewrite sx32_lit by lia. zstep. change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0). zstep. fold_lits.
rewrite Z.lor_0_r. zstep. if_cases K1; zify_cond K1. 2:{ exfalso. clear -K1 SZ. lia. }
zstep. zstep. zstep. if_cases K2; zify_cond K2. { exfalso. clear -K2. lia. }
zstep. zstep.
let x1 := reg_val 1%Z in let x2 := reg_val 2%Z in let x5 := reg_val 5%Z in let x6 := reg_val 6%Z in let x7 := reg_val 7%Z in
let x8 := reg_val 8%Z in let x9 := reg_val 9%Z in let x11 := reg_val 11%Z in let x12 := reg_val 12%Z in let x13 := reg_val 13%Z in
let x14 := reg_val 14%Z in let x15 := reg_val 15%Z in let x16 := reg_val 16%Z in let x17 := reg_val 17%Z in let x18 := reg_val 18%Z in
let x19 := reg_val 19%Z in let x20 := reg_val 20%Z in let x21 := reg_val 21%Z in let x28 := reg_val 28%Z in let x29 := reg_val 29%Z in
let x30 := reg_val 30%Z in let x31 := reg_val 31%Z in
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
assert (REST : forall x10, evtF bsegs RNG nstore_post (MS (mkR x1 x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0x7079c) fc None mc (seg_rom bsegs)))
end.
2:{ zstep. if_cases K3; zify_cond K3; [apply REST|]. zstep. replace (Z_to_bv 64 255) with (Z_to_bv 64 sz) by (f_equal; clear -K3 SZ; lia). apply REST. }
intros x10.
zstep. zstep. zstep. do 4 zstep. zstep.
carve_frame 16%nat ST.
do 5 zstep. amo_step.
zstep. zstep. shr0. zstep. zstep. shr0.
zstep. if_cases K4; zify_cond K4. { exfalso. clear -K4. lia. }
zstep. shr0.
zstep. if_cases K5; zify_cond K5. 2:{ exfalso. clear -K5. lia. }
zstep. zstep. zstep. zstep. zstep. if_cases K6; zify_cond K6. { exfalso. clear -K6 STOB. unfold AIMG_HI in STOB. lia. }
zstep. zstep. zstep.
match goal with |- context [Z.shiftr ?e 41] =>
replace (Z.shiftr e 41) with (8 * tf)%Z
by (rewrite Z.shiftl_mul_pow2 by lia;
first [ change 18446744073709551615%Z with (Z.ones 64); rewrite Z.land_ones by lia
| change 18446744073709551616%Z with (2^64)%Z ];
rewrite Z.mod_small by lia; rewrite Z.shiftr_div_pow2 by lia;
change (2^44)%Z with (8 * 2^41)%Z; rewrite Z.mul_assoc, Z.div_mul by lia; lia)
end.
do 3 zstep. zstep.
zstep. if_cases K7; zify_cond K7. { exfalso. clear -K7 STOB TF. unfold AIMG_HI in STOB. lia. }
zstep. zstep. zstep. rewrite Z.lor_0_l.
apply (proj1 (rw_cells_app bsegs _ _ [_] _)) in FRM. destruct FRM as [FRM FR2]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FR2.
remember (STORE + 8 * tf)%Z as FA eqn:EFA.
zstep. zstep. zstep.
set (SRC := firstn (Z.to_nat (8 * sz)) (u64s tb)).
assert (LSRC : length SRC = Z.to_nat (8 * sz)) by (subst SRC; rewrite firstn_length, u64s_length, LTB; lia).
replace (Z.shiftl sz 3) with (Z.of_nat (length SRC)) by (rewrite LSRC, Z.shiftl_mul_pow2 by lia; lia).
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
assert (TBc : bytes_at bsegs mc T (SRC ++ skipn (Z.to_nat (8 * sz)) (u64s tb)))
by (subst SRC; rewrite firstn_skipn; match goal with H : u64arr bsegs mc T tb |- _ => exact (proj1 H) end);
assert (DSTc : rw_cells bsegs mc (FA + 8) [CB (length SRC) jf]) by (rewrite LSRC; assumption)
end.
zstep.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
eapply evtF_cut;
[ eapply (imemcpy_specZ RNG) with (src := SRC) (rest := skipn (Z.to_nat (8 * sz)) (u64s tb)) (junk := jf);
[ eassumption | exact TBc | exact DSTc | reflexivity
| rewrite length_app, skipn_length, u64s_length, LTB, LSRC; unfold sf_hide in *; lia
| rewrite LSRC; lia | rewrite length_app, skipn_length, u64s_length, LTB, LSRC; lia | rewrite LSRC; lia
| rewrite LSRC; eapply rng_sub'; [exact RT | lia] | rewrite LSRC; eapply rng_sub'; [exact RFR | lia] ]
| (post_call bsegs mc) ]
end.
zstep. zstep. zstep.
replace (Z.land (Z.shiftr tf 16) 18446744073709551600) with 0%Z.
2:{ change 18446744073709551600%Z with (2^64 - 2^4)%Z. rewrite land_align_down by (shr0; try lia; rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
rewrite Z.shiftr_div_pow2 by lia. Z.div_mod_to_equations. lia. }
zstep. zstep. fold_lits. amo_stepW4. rewrite sx32_lit by lia.
zstep. zstep. zstep. shr0.
zstep. zstep. zstep.
match goal with H : rw_cells bsegs _ (bv_unsigned sp + -96) (C8 (Z_to_bv 64 tf) :: ?rest) |- _ =>
apply (rw_cells_C8_C4C4 bsegs _ _ [] rest tf) in H; [cbn [app] in H | lia] end.
zstep. rewrite sx32_lit by lia. zstep.
setreg 10%Z (Z_to_bv 64 0)
ltac:(f_equal; symmetry;
match goal with |- Z.b2z (Z.lxor ?y 1048576 <? 1)%Z = 0%Z =>
replace y with (sz + 1 + tf)%Z
by (try change 4294967295%Z with (Z.ones 32); try change 18446744073709551615%Z with (Z.ones 64);
rewrite ?Z.land_ones by lia; try change (2^32)%Z with 4294967296%Z; try change (2^64)%Z with 18446744073709551616%Z;
symmetry; Z.div_mod_to_equations; lia) end;
change 1048576%Z with (2^20)%Z; rewrite zb_lxor_pow2_small by lia;
replace (_ <? 1) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
zstep. zstep. zstep. try rewrite sx32_lit by lia.
do 9 zstep.
zstep. zstep. zstep. if_cases K8; zify_cond K8. { exfalso. clear -K8. lia. }
do 4 zstep.
match goal with FR1 : rw_cells bsegs _ (bv_unsigned sp + -112) _, ST : stk bsegs _ lo _ |- _ => release_frame FR1 ST (bv_unsigned sp + -96)%Z end.
match goal with FR0 : rw_cells bsegs _ (bv_unsigned sp + -96) _, ST : stk bsegs _ lo _ |- _ => release_frame FR0 ST (bv_unsigned sp + -32)%Z end.
match goal with FR : rw_cells bsegs _ (bv_unsigned sp + -32) _, ST : stk bsegs _ lo _ |- _ => release_frame FR ST (bv_unsigned sp) end.
match goal with CTF : rw_cells bsegs _ 1524744 _ |- _ => cbn [amo_val] in CTF; rewrite lit_add_lit in CTF end.
apply evtF_done. unfold nstore_post. subst FA. unfold sf_hide in *.
replace (bv_unsigned sp - 112)%Z with (bv_unsigned sp + -112)%Z by lia.
replace (tf + (sz + 1))%Z with (tf + sz + 1)%Z in * by lia.
do 16 eexists. split; [reflexivity|].
repeat match goal with |- _ /\ _ => split end; try assumption.
- match goal with H : rw_cells bsegs _ NDp _ |- _ =>
rewrite bv_swrap_small in H by (change (bv_half_modulus 32) with 2147483648%Z; lia); exact H end.
- fold SRC. apply (proj2 (rw_cells_app bsegs _ _ [_] _)). split; [assumption|].
cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. rewrite <- LSRC. assumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End NStore.
End NStoreFile.
Section HashLoop.
Variables (RNG : footprint)
(ra sp gp tp t0 t1 t2 s0 s1 a3 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (T sz : Z) (tb : list word).
Hypothesis TB : u64arr bsegs m T tb.
Hypothesis LTB : length tb = 255%nat.
Hypothesis SZ : (1 <= sz <= 255)%Z.
Hypothesis TBB : (0 <= T /\ T + 2040 <= 2^47)%Z.
Hypothesis RT : rng RNG T 2040.
#[using="TB LTB SZ TBB RT"] Lemma hash_loop : forall (k : nat) (i h : Z) x15 x16 (Q : machine_state -> Prop),
Z.to_nat (sz - i) = k -> (0 <= i < sz)%Z -> (0 <= h < 2^64)%Z ->
(forall x15' x16',
evtF bsegs RNG Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 14313749767032793493) (Z_to_bv 64 (T + 8 * sz))
(Z_to_bv 64 (mz_adds h (map bv_unsigned (firstn (Z.to_nat (sz - i)) (skipn (Z.to_nat i) tb)))))
a3 (Z_to_bv 64 (T + 8 * sz)) x15' x16' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x72e14) fc None m (seg_rom bsegs))) ->
evtF bsegs RNG Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 14313749767032793493) (Z_to_bv 64 (T + 8 * i)) (Z_to_bv 64 h)
a3 (Z_to_bv 64 (T + 8 * sz)) x15 x16 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x72df0) fc None m (seg_rom bsegs)).
Proof.
Local Ltac2 Set LiaHints.tbl := fun () => "00D0>10353725385.5111293233672.5525607159172.5541348280724.5743622467737.5543935889328.5545579985956.6045579985963.6151441913051.5352781141368.5554468097430.6254468097432.6056660910639.5559310648043.5059314923118.4759586081460.6059586081465.6359586081466.6262759001015.5567789172792.5500000;00I00[00f01401F01G01H01S01[01c01k02902K02V02^02f02n03<03GS3LTB2Hk2HiS3LTB2Hk2Hi2KBS3LTB2SZ3TBB2Hk2HiS3LTB2Hk2HiS3LTB2Hk2Hi2KBS3LTB2SZ3TBB2Hk2HiFFS3LTB2Hk2HiS3LTB2HkS3LTB2HkS3LTB2HkS3LTB2Hk2Hi2KBS3LTB2SZ2Hk2Hi3NTHS3LTB2Hk2HiS3LTB2HkS3LTB2HkS3LTB2HkS3LTB2SZ2Hk2HiS3LTB2Hk2Hi".
induction k as [|k IH]; intros i h x15 x16 Q Hk Hi Hh K; [exfalso; lia|].
destruct (nth_error tb (Z.to_nat i)) as [w|] eqn:NTH. 2:{ exfalso. apply nth_error_None in NTH. rewrite LTB in NTH. lia. }
pose proof (u64arr_read bsegs m T tb i w (wa (T + 8 * i)) TB NTH ltac:(lia) eq_refl) as RD.
do 8 zstep.
lazymatch goal with |- context [Z_to_bv 64 (Z.lxor ?a h * ?M)%Z] =>
replace (Z_to_bv 64 (Z.lxor a h * M)%Z) with (Z_to_bv 64 (mz_add h (bv_unsigned w)))
by (unfold mz_add, mz_mix; apply Z_to_bv_mod64) end.
pose proof (mz_add_range h (bv_unsigned w)) as Hh'.
assert (SK : skipn (Z.to_nat i) tb = w :: skipn (Z.to_nat (i + 1)) tb).
{ replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
clear - NTH. revert NTH. generalize (Z.to_nat i) as n. intros n NTH.
revert tb NTH. induction n as [|n IHn]; intros [|x l] NTH; cbn in *; try discriminate.
- injection NTH as ->. reflexivity.
- apply IHn. exact NTH. }
zstep. if_cases KB; zify_cond KB.
- replace (T + 8 * i + 8)%Z with (T + 8 * (i + 1))%Z by lia.
eapply (IH (i + 1)%Z); [lia | lia | exact Hh' |].
intros x15' x16'.
replace (mz_adds (mz_add h (bv_unsigned w)) (map bv_unsigned (firstn (Z.to_nat (sz - (i + 1))) (skipn (Z.to_nat (i + 1)) tb))))
with (mz_adds h (map bv_unsigned (firstn (Z.to_nat (sz - i)) (skipn (Z.to_nat i) tb)))); [apply K|].
rewrite SK. replace (Z.to_nat (sz - i)) with (S (Z.to_nat (sz - (i + 1)))) by lia. cbn [firstn map mz_adds fold_left]. reflexivity.
- replace (T + 8 * i + 8)%Z with (T + 8 * sz)%Z by lia.
replace (mz_add h (bv_unsigned w)) with (mz_adds h (map bv_unsigned (firstn (Z.to_nat (sz - i)) (skipn (Z.to_nat i) tb)))); [apply K|].
rewrite SK. replace (Z.to_nat (sz - i)) with 1%nat by lia. cbn. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End HashLoop.
Section FindFile.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.
Section FindLoop.
Variables (RNG : footprint)
(ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s4 s5 s7 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (hsh NODES N : Z) (hs lk sid : Z -> Z).
Hypothesis Hh : (0 <= hsh < 2^64)%Z.
Hypothesis HN : (1 <= N < 65536)%Z.
Hypothesis MI : mem_inv bsegs m.
Hypothesis CMAP : rw_cells bsegs m MAP1 [C8 (Z_to_bv 64 NODES)].
Hypothesis CN : forall i, (1 <= i <= N)%Z ->
rw_cells bsegs m (NODES + 16 * i) [C8 (Z_to_bv 64 (hs i)); C4 (Z_to_bv 64 (lk i)); C4 (Z_to_bv 64 (sid i))].
Hypothesis NB : (AIMG_HI <= NODES /\ NODES + 1048576 <= ATOP /\ NODES mod 4096 = 0)%Z.
Hypothesis LK : lk_ok lk N.
Hypothesis HS : forall i, (1 <= i <= N)%Z -> (0 <= hs i < 2^64)%Z.
Hypothesis RI : rng_aimg RNG.
Hypothesis RNODES : rng RNG NODES 1048576.
#[warnings="-notation-for-abbreviation"] Notation ST_AT pc x10 x11 x12 :=
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 x12 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 hsh) s4 s5 (Z_to_bv 64 0xffff) s7 (Z_to_bv 64 MAP1) s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None m (seg_rom bsegs)).
#[using="rc NODES sid Hh HN CMAP CN NB LK HS RI RNODES"] Lemma find_loop : forall (k : nat) (j : Z) x10 x12 (Q : machine_state -> Prop),
(Z.to_nat j <= k)%nat -> (0 <= j <= N)%Z ->
(forall j' x11 x12', (1 <= j' <= N)%Z -> hs j' = hsh -> In j' (chain lk j) ->
evtF bsegs RNG Q (ST_AT 0x72f84 (Z_to_bv 64 j') x11 x12')) ->
(forall x10' x12', Forall (fun j' => hs j' <> hsh) (chain lk j) ->
evtF bsegs RNG Q (ST_AT 0x72ed8 x10' (Z_to_bv 64 0) x12')) ->
evtF bsegs RNG Q (ST_AT 0x72e80 x10 (Z_to_bv 64 j) x12).
Proof.
unfold AIMG_HI, MAP1 in *.
induction k as [|k IH]; intros j x10 x12 Q Hk Hj FOUND ABSENT.
- Local Ltac2 Set LiaHints.tbl := fun () => "00P0>18204077971.7121921109347.6321921109347.642597469165.71 28915217076.7132579247557.6332954672962.6232963790148.7032963790154.7334612439040.7136511323770.6336511323770.6440140147424.6540818989526.6445281471074.7148788237276.7452843860937.765798337359.65 59308628179.1 59314873579.6359314873579.6459586081460.7160210310797.5860210310797.5960210310797.6060210310797.6160210310797.6563118856890.6663852889314.6465504523926.6365504523926.649124237546.55 00000E00R00_00c00g00n01;01H01U01V01c02002;02?02F02[02_03003403B03L03P03Z03d04204@04N04_04c04g04k055S2HN2NB2Hk2Hj3ENA3LKjS2HN2NB2Hk2HjS2HN2NB2Hk2HjS2HkS2HkS2NB2HkS2HN2NB2Hk2HjS2HN2NB2Hk2HjS2HN2NB2Hk2HjFS2HN2NB2Hk2HjS2HN2NB2Hk2HjS2NB2Hk3LKjS2HkS2Hk2HjS2HN2NB2Hk2Hj3ENA3LKjS2HkS2HN2NB2Hk2Hj3LKjS2K0S2NB2Hk3LKj2K0S2NB2Hk2K1S2HkS2Hk2Hj2NZS2Hk2Hj2NZS2NB2Hk2Hj3LKjS2NB2Hk2Hj3LKjS2NB2Hk2Hj3LKjS2HN2NB2Hk2Hj3LKjS2HkS2HkS2HkS2NB2Hk2Hj".
assert (j = 0%Z) by lia. subst j.
zstep. if_cases K0; zify_cond K0. 2:{ exfalso. clear -K0. lia. }
apply ABSENT. rewrite chain_0. constructor.
- destruct (Z.eq_dec j 0) as [->|NZ].
{ zstep. if_cases K0; zify_cond K0. 2:{ exfalso. clear -K0. lia. } apply ABSENT. rewrite chain_0. constructor. }
pose proof (CN j ltac:(lia)) as NODE. pose proof (LK j ltac:(lia)) as LKj. pose proof (HS j ltac:(lia)) as HSj.
pose proof (chain_cons lk N j LK ltac:(lia)) as CC.
zstep. if_cases K0; zify_cond K0. { exfalso; lia. }
zstep. zstep.
replace (bv_swrap 32 (Z.shiftr (bv_wrap 32 j) 16)) with 0%Z
by (rewrite bv_wrap_small by (change (bv_modulus 32) with 4294967296%Z; lia); rewrite Z.shiftr_div_pow2, Z.div_small by lia; reflexivity).
do 3 zstep.
zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
do 5 zstep.
setreg 11%Z (Z_to_bv 64 (NODES + 16 * j))
ltac:(f_equal; rewrite Z.mod_small by lia; change 65535%Z with (Z.ones 16); rewrite Z.land_ones by lia;
rewrite Z.mod_small by lia; rewrite Z.shiftl_mul_pow2 by lia; lia).
remember (NODES + 16 * j)%Z as NA eqn:ENA.
zstep. zstep. rewrite sx32_lit by lia.
subst NA.
zstep. if_cases K2; zify_cond K2.
+
eapply (IH (lk j)); [lia | lia | |].
* intros j' x11 x12' H1 H2 H3. apply FOUND; [exact H1 | exact H2 |]. rewrite CC. right. exact H3.
* intros x10' x12' FA. apply ABSENT. rewrite CC. constructor; [| exact FA]. clear -K2. intros E. apply K2. rewrite E. reflexivity.
+
zstep. apply FOUND; [lia | | rewrite CC; left; reflexivity]. clear -K2 Hh HSj. first [exact K2 | symmetry; exact K2 | lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End FindLoop.
End FindFile.
End CANSEC3.
