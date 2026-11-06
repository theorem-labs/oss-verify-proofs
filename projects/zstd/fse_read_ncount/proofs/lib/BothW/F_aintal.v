(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Arr InitMem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import StrFun.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg ABase AQConst.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StepF StrwF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import AKit AKit2 AKitQ.
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

Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section CANSEC1. Context {rc : runConstT}.
Definition imemset_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(a0 a4 a5 a6 a7 : word) (A n : Z) (m : amem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3' t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom bsegs)
/\ munch [(A, A + n)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ rw_cells bsegs m' A [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))].
Section IMemset.
Variables (RNG : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : amem).
Hypothesis MI0 : mem_inv bsegs m.
Hypothesis AB : bv_unsigned a0 + bv_unsigned a2 < 2^64 /\ 0 < bv_unsigned a2.
Hypothesis RR : rng RNG (bv_unsigned a0) (bv_unsigned a2).
Notation A := (bv_unsigned a0).
Notation n := (bv_unsigned a2).
Notation W := [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z.
Notation POST := (imemset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a4 a5 a6 a7 (bv_unsigned a0) (bv_unsigned a2) m).
Notation ST pc mm x11 x12 x13 :=
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 x11 x12 x13 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
Ltac with_arr tac :=
lazymatch goal with
| ARR : u8arr ?segs ?m ?A ?bs, FIL : filled ?cb ?bs _, LEN : length ?bs = _ |- _ => tac segs ARR FIL LEN A cb
end.
Ltac fin_with cover :=
zstep;
with_arr ltac:(fun segs ARR FIL LEN A cb =>
let E := fresh "E" in
pose proof (filled_all _ _ _ FIL ltac:(cover)) as E;
rewrite LEN in E; rewrite E in ARR;
apply rw_cells_of_u8arr in ARR; rewrite repeat_length in ARR);
unfold imemset_post; finish; subst; assumption.
Lemma imemset_bloop : forall (K : nat) (i : Z) (m1 : amem) (bs : list byte) (Q : Z -> Prop),
Z.to_nat (n - i) = K ->
u8arr bsegs m1 A bs -> filled (Z_to_bv 8 0) bs Q -> length bs = Z.to_nat n ->
mem_inv bsegs m1 -> munch W m m1 -> wmono bsegs m m1 ->
(forall j, 0 <= j < i -> Q j) -> 0 <= i < n ->
forall x13, x13 = Z_to_bv 64 (A + i) ->
evtF bsegs RNG POST (ST 0x64210 m1 (Z_to_bv 64 0) (Z_to_bv 64 (A + n)) x13).
Proof using AB RR.
pose proof (bv_unsigned_in_range 64 a0) as R0. unfold bv_modulus in R0. cbn in R0.
induction K as [K IH] using lt_wf_ind; intros i m1 bs Q HK ARR FIL LEN MI MU WM HQ Hi x13 ->.
Local Ltac2 Set LiaHints.tbl := fun () => "0090>11469010974.5812527860964.5519628481055.5531168967626.5835987002189.555120842925.58 67692313067.547739161719.55 8929161887.55 00000=00K00\01201@01K01\01d025S2HK3LEN2Hj1lS2HK2Hi3LEN2KKS2AB2R02HK2Hi3LENS2HK3LEN2Hj1l2AB2Hi2KKS2AB2HK2Hi3LENS2HK3LEN2HiS2AB2R02HK3LEN2HiS2HK3LENS2AB2R02HK2Hi3LEN".
mst i 1%nat ltac:(reflexivity).
zstep. zstep. if_cases KK; zify_cond KK.
-
eapply (IH (Z.to_nat (n - (i + 1))) ltac:(lia) (i + 1) _ _ _ eq_refl ARR FIL LEN MI MU WM); [|lia|f_equal; lia].
intros j Hj. destruct (Z_lt_le_dec j i); [left; apply HQ; lia| right; lia].
- zstep. fin_with ltac:(intros j Hj; destruct (Z_lt_le_dec j i); [left; apply HQ; lia| right; lia]).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma imemset_wloop : forall (K : nat) (i : Z) (m1 : amem) (bs : list byte) (Q : Z -> Prop),
Z.to_nat (n - i) = K ->
u8arr bsegs m1 A bs -> filled (Z_to_bv 8 0) bs Q -> length bs = Z.to_nat n ->
mem_inv bsegs m1 -> munch W m m1 -> wmono bsegs m m1 ->
(forall j, 0 <= j < i -> Q j) -> 0 <= i < n -> (exists q, i = 16 * q) -> (exists q, n = 16 * q) ->
forall x13, x13 = Z_to_bv 64 (A + i) ->
evtF bsegs RNG POST (ST 0x64244 m1 (Z_to_bv 64 0) (Z_to_bv 64 (A + n)) x13).
Proof using AB RR.
pose proof (bv_unsigned_in_range 64 a0) as R0. unfold bv_modulus in R0. cbn in R0.
induction K as [K IH] using lt_wf_ind; intros i m1 bs Q HK ARR FIL LEN MI MU WM HQ Hi [qi Hqi] [qn Hqn] x13 ->.
Local Ltac2 Set LiaHints.tbl := fun () => "00?0>11469010974.6215334889917.6215524692031.5922522182488.5832466410975.693256324148.63 34339459430.6335987002189.5940132705702.7045230111716.5950278918646.5950432419481.5966492033975.5967694409198.588929161887.59 00000=00S00l01E01[02202?02P02X02f03803J03R03k04DS2HK3LEN2Hj1lS2AB2HK3LEN2Hi3Hqi3HqnS2AB2R02HK2Hi3Hqi3Hqn3LENS2AB2R02HK2Hi3Hqi3Hqn3LENS2AB2HK2Hi3Hqi3Hqn3LENS2HK3LEN2Hj2l02AB2Hi2KKS2HK3LEN1l2l0S2AB2HK2Hi3LEN2KKS2HK3LENS2HK2Hi3LEN2KKS2AB2HK2Hi3Hqi3LENS2AB2HK2Hi3Hqn3LENS2HK3LENS2AB2R02HK3LEN2Hi3Hqi3HqnS2AB2R02HK2Hi3Hqi3Hqn3LEN".
mst i 8%nat ltac:(reflexivity).
mst (i + 8)%Z 8%nat ltac:(reflexivity).
zstep. zstep. if_cases KK; zify_cond KK.
- eapply (IH (Z.to_nat (n - (i + 16))) ltac:(lia) (i + 16) _ _ _ eq_refl ARR FIL LEN MI MU WM); [|lia| exists (qi + 1); lia| exists qn; lia| f_equal; lia].
intros j Hj. destruct (Z_lt_le_dec j i); [left; left; apply HQ; lia|]. destruct (Z_lt_le_dec j (i + 8)); [left; right; lia| right; lia].
- fin_with ltac:(intros j Hj; destruct (Z_lt_le_dec j i); [left; left; apply HQ; lia|];
destruct (Z_lt_le_dec j (i + 8)); [left; right; lia| right; lia]).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma imemset_body : forall junk,
rw_cells bsegs m A [CB (Z.to_nat n) junk] ->
evtF bsegs RNG POST (ST 0x641f8 m (Z_to_bv 64 0) a2 a3).
Proof using AB MI0 RR.
intros junk DST. pose proof MI0 as MI.
pose proof (bv_unsigned_in_range 64 a0) as R0. unfold bv_modulus in R0. cbn in R0.
pose proof (munch_refl W m) as MU. pose proof (wmono_refl bsegs m) as WM.
pose proof (u8arr_of_rw_cells _ _ _ _ _ DST) as ARR.
pose proof (rw_cells_CB_length _ _ _ _ _ DST) as LEN.
pose proof (filled_init (Z_to_bv 8 0) junk) as FIL.
zstep. zstep.
zstep. Local Ltac2 Set LiaHints.tbl := fun () => "00:0>40825300077.5043549202818.4943549254066.5043833420478.5054385497688.5055514599560.5059308586377.5159308586377.5259308628304.4960706498226.4800000500=00E00V00[00i01101901D01IS3LENS2AB3LENS2AB3LENS2AB2R03LEN2Kn2KAS3LENS2AB2R03LEN2HAS3LEN2HjS3LEN2HjS2AB3LEN2K1S3LEN".
if_cases K0; zify_cond K0.
-
zstep. if_cases K1; zify_cond K1; [exfalso; lia|].
do 7 zstep. zstep.
assert (HA : A mod 16 = 0 /\ n mod 16 = 0).
{ rewrite Z.land_lor_distr_l in K0. apply Z.lor_eq_0_iff in K0. destruct K0 as [Kn KA].
change 15 with (Z.ones 4) in Kn, KA. rewrite Z.land_ones in Kn, KA by lia. change (2^4) with 16 in Kn, KA. lia. }
eapply (imemset_wloop (Z.to_nat (n - 0)) 0 m _ _ eq_refl ARR FIL LEN MI MU WM); [intros j Hj; lia| lia| exists 0; lia| exists (n / 16); lia| symmetry; apply Z_to_bv_plus0].
-
zstep. if_cases K1; zify_cond K1; [exfalso; lia|].
zstep. zstep.
eapply (imemset_bloop (Z.to_nat (n - 0)) 0 m _ _ eq_refl ARR FIL LEN MI MU WM); [intros j Hj; lia| lia| symmetry; apply Z_to_bv_plus0].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End IMemset.
#[using="Type"] Lemma imemset_spec : forall (A n : Z) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : amem) (junk : list byte),
a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 0 -> a2 = Z_to_bv 64 n -> 0 <= A -> 0 < n -> A + n < 2^64 ->
rw_cells bsegs m A [CB (Z.to_nat n) junk] ->
mem_inv bsegs m ->
rng RNG A n ->
evtF bsegs RNG (imemset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a4 a5 a6 a7 A n m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x641f8) fc None m (seg_rom bsegs)).
Proof.
intros until junk. intros -> -> -> HA Hn HAn DST MI RR.
pose proof (imemset_body RNG ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m MI) as H.
Local Ltac2 Set LiaHints.tbl := fun () => "0030>28807763462.435619512016.43 61927656618.4300000;00C00NS2HA2Hn3HAnS2Hn3HAnS2HA2Hn3HAn".
rewrite !unsigned_lit in H by lia. apply (H ltac:(lia) RR junk DST).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition ia_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a7 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (m : amem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0xa3740) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom bsegs)
/\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0xa3740, 0xa3740 + 0x81030); (0x131fc8, 0x131fc8 + 4)]%Z m m'
/\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ stk bsegs m' lo (bv_unsigned sp)
/\ rw_cells bsegs m' 0x131fc8 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
/\ stk bsegs m' 0xa3740 (0xa3740 + 0x81030)
/\ (forall j, 0 <= j < 32768 -> bytes_at bsegs m' (0xa3748 + 8 * j) (le8 (Z_to_bv 64 0))).
#[using="Type"] Lemma internal_allocator_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : amem) (ia : bool) (lo : Z),
stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 ->
mem_inv bsegs m ->
rw_cells bsegs m AIA_FLAG [C1 (Z_to_bv 8 (if ia then 1 else 0)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
stk bsegs m AIA_BASE (AIA_BASE + AIA_SIZE) ->
(ia = true -> forall j, 0 <= j < AIA_MAP1_LEN / 8 -> bytes_at bsegs m (AIA_MAP1 + 8 * j) (le8 (Z_to_bv 64 0))) ->
rw_cells bsegs m 0x998f0 [C8 (Z_to_bv 64 0x131fe0)] -> rw_cells bsegs m 0x131fe0 [C8 (Z_to_bv 64 4096)] ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
evtF bsegs RNG (ia_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a7 F fc lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x5e6f8) fc None m (seg_rom bsegs)).
Proof.
intros until lo. intros ST CEIL LO MI FL IA Z2 PG1 PG2 RIMG RSTK.
unfold AIA_FLAG, AIA_BASE, AIA_SIZE, AIA_MAP1, AIA_MAP1_LEN in *.
word_range sp SPR.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
Local Ltac2 Set LiaHints.tbl := fun () => "03C0?10177642990.61 10211132774.12210512138478.64 11652032566.85 11676815974.12211805467289.61 11805467289.62 11805467289.63 11805467289.64 12208768790.10812208768790.98 12622667366.1221303713722.76  1337250677.69  1337250677.83  15047932149.83 15047932149.84 1522605749.122 15482755935.10015547002357.11115833765478.12216791921141.11217776320428.61 17776320431.11617776320431.61 1800609155.117 1800609155.62  1800609155.63  18030819016.86 1819542645.111 1878909846.86  18930958230.70 18930958230.81 19020901987.11219418166041.55 1998156082.110 20404037910.11120404037910.56 21311471409.12221459134830.63 21551587250.67 21916162286.64 21921109347.11522364832150.10722389541692.61 22478859706.12222577726822.12222700267513.10122700267513.11322700267513.56 22700267513.57 22700267513.59 22700267513.71 22700267513.85 22844925014.11823189841850.12223309688626.99 23312727126.11823431052529.11824638473347.11824638473347.62 24638473347.63 2468716872.98  24959551930.76 25882472949.10026494647592.11826494647592.12226494647592.54 26494647592.76 27907200258.54 27907201564.10928417259964.63 28535651182.63 28857563758.62 29756113686.56 29756113686.70 30343067833.53 30585842504.70 30811659117.69 30811659117.70 30811659117.83 30958019910.70 31378308326.54 31580275445.11131907890165.11132440122478.62 33548873814.11833680001082.64 33866789857.11834273227862.11834430152252.64 35012330478.63 35990850454.98 36053481878.79 36115622446.11736115622447.61 36115622447.62 36157221978.56 37396808821.99 37639609914.12237849467958.66 37945682572.82 38166047726.63 38589418426.76 3862333128.56  38884027061.76 39208223342.62 39224602138.54 39906581621.99 40457739452.62 41008054706.69 41008054706.83 41165775410.87 41349894980.12242426800622.61 43059266230.52 4325121141.111 43987951406.11743987951406.62 43987951406.63 43988483203.11643988483203.61 44072505832.11244552480493.11145221239098.63 45266465884.82 45848756903.61 46468661564.63 46609722344.11247279694931.54 4761726581.69  4761726581.83  48716850061.12248716850061.54 49005433153.12249190166253.99 49649769127.64 50347881823.84 5087518190.63  51711223320.10851711223320.53 51748900282.12252084006669.12252105090727.63 53375371158.86 53375371158.97 53619353077.99 53767577775.11653767577775.61 53767577775.62 54243526019.11754243526019.62 54262026646.96 563227834.62   56512821749.11156674771350.65 57022093363.54 57622410744.11757745675194.63 57774270518.10858124020905.11858124020905.12258420675341.76 58855658678.68 59021008717.97 59714667374.63 59751645429.69 59751645429.83 59922006389.69 59922006389.83 60168063930.12260858483367.63 61482382924.54 61743887418.12261743887418.54 6239253050.122 6239253050.54  62700355130.12262826138350.64 62933954610.69 62942113067.11263235321900.11563235321900.60 63305555623.62 63371158710.83 63904671472.12264453876959.11264666651381.99 64980110325.99 64997134979.11864997134979.63 64997134979.64 65256630714.55 65602308597.99 65808723540.11866260016006.11766260016006.59 66400913390.61 66687629877.12266687629877.54 67129861050.12267854013288.11267964909362.11168402660080.76 707959894.118  7450259002.122 748001722.76   7920514928.122 7920514928.54  8583720762.61  9854410738.112 00000900:00C00D00E00F00G00H00I00J00K00L00M00N00O00P00Q00Z00[00\00]00^00b00f00j00k00l00m00n00o01001101201301401501601701801A01B01K01O01P01T01U01V01Y01\01`01d02502802;02<02=02C02D02M02N02O02P02Q02R02S02T02U02V02W02[02_02c02l03503603703803903B03C03L03M03N03O03P03Y03Z03_03`03a03e03n03o04004404804<04@04A04B04C04G04P04Q04R04[04d04e04f04j05005605705805A05E05F05J05N05R05S05T05U05^05c05g05h05l05m05n05o06006106206;06D06E06F06O06P06Q06R06S06T06U06V06W06[06_06c06d06e06f06k06l06m06n07507:07;07<07=07>07?07@07I07J07K07L07M07N07O07P07Q07R07S07T07U07^07_07`07d07h07i07j07k07l07m07n07o08008108208308408;08B08K08T08]08^08_08e08f08g08h08i08j08k090091S4CEIL2LOSS4CEIL2LOSSSSSSSSSSSSSFS4CEIL2LOFSSFS2LOS2LOS2LOSSSSSSSSSSSSSSS4CEIL2LOSS4CEIL2LOS2HjSS2HBSSS1HS1HS2HqS2HqS4CEIL2LO2Hj2Hi1HS1HS1HSSS4CEILSS4CEIL2LOSSSSSFSSSSS2LOS2LOS2HBS4CEIL2LOS4CEIL2LOSSSSS4CEIL2LOFS4CEIL2LOFSSSS4CEIL2LOSS3SPRSSS2HBS4CEIL2LOSSS2LOS2LOS2LOS2HjSSSS2HjS4CEIL2LOSSS4CEIL2LOS4CEIL2LOSSS2HBS4CEILS4CEILSSS4CEIL2LOS2LOSS2LOS2LOS2LOSSSS4CEIL2LOS3SPRS2HjSS2HBSSSSSSS4CEIL2LOS4CEIL2LOSFS4CEIL2LOSSSSSSSSS2LOS2LOS2LOSSSS3SPRSSSS2Hj2HiS3SPRSSSSSSS4CEIL2LOSSSSSSSSSSSSS4CEIL2LOSSS2LOS2LOSSSFSSSSSSSSS2Hj2HiS2Hj2HiS4CEIL2LOS4CEIL2LOS4CEIL2LOSSS4CEILSSSSSSS3SPRS".
carve_frame 48%nat ST.
do 6 step.
step. zstep.
destruct ia.
-
lstep. step. step. if_lit.
step. zstep.
do 7 step.
release_frame FR ST (bv_unsigned sp).
unfold ia_post. finish.
+ eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; intros q Hq; lia.
+ intros j Hj. pose proof (Z2 eq_refl j ltac:(lia)) as B. eapply bytes_at_agree; [exact B|].
intros i Hi. apply MU. cbn [outside]. rewrite length_le8 in Hi. rewrite wa_unsigned by lia. lia.
-
apply (munch_weaken _ [(bv_unsigned sp - 48, bv_unsigned sp); (0xa3740, 0xa3740 + 0x81030); (0x131fc8, 0x131fc8 + 4)]%Z) in MU.
2:{ unfold sub_fp; cbn [outside]; intros q Hq; lia. }
clear Z2.
lstep. step. step. if_lit.
do 8 zstep.
apply (rw_C1x4_to_C4 _ _ 0 0 ltac:(lia) ltac:(lia)) in FL. change (0 + 256 * 0) with 0 in FL.
amo_step. lits.
do 4 zstep.
amo_step.
step. if_lit.
zstep. zstep. step. if_lit.
apply (rw_C4_to_C1x4 _ _ 0 1 ltac:(lia) ltac:(lia)) in FL.
lstep. step. if_lit.
step. step. zstep. zstep. zstep. step. step.
carve_frame 40%nat IA.
step. call (imemset_spec 0x124748 40); [reflexivity| reflexivity| reflexivity| lia| lia| lia| exact FR0| assumption|].
rename POST into Z1.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
destruct (stk_split bsegs mm 0xa3740 0xa3748 (669504 + 528392) IA ltac:(lia)) as [IA0 IA1] end.
clear IA.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
destruct (stk_cb mm 0xa3740 0xa3748 IA0 ltac:(lia)) as [junk1 FR1] end.
clear IA0. change (Z.to_nat (0xa3748 - 0xa3740)) with 8%nat in FR1.
step.
step. step. step. step.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
destruct (stk_split bsegs mm 0xa3748 0xe3748 (669504 + 528392) IA1 ltac:(lia)) as [IA2 IA3] end.
clear IA1.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
destruct (stk_cb mm 0xa3748 0xe3748 IA2 ltac:(lia)) as [junk2 DST2] end.
clear IA2. change (0xe3748 - 0xa3748) with 0x40000 in DST2.
step. call (imemset_spec 0xa3748 0x40000); [reflexivity| reflexivity| reflexivity| lia| lia| lia| exact DST2| assumption|].
rename POST into Z2.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
assert (MAP : forall j, 0 <= j < 32768 -> bytes_at bsegs mm (0xa3748 + 8 * j) (le8 (Z_to_bv 64 0)))
by (intros j Hj; apply (cb_zero_le8 _ _ _ _ Z2); lia);
pose proof (stk_of_cb mm 0xa3748 0x40000 _ Z2 ltac:(lia)) as IA2 end.
clear Z2. box MAP. snapshot [(0xe3780, 0x124748); (0x131fc8, 0x131fcc)]%Z MUm WMm.
zstep. zstep. step. step. step.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
destruct (stk_split bsegs mm 0xe3748 0xe3780 (669504 + 528392) IA3 ltac:(lia)) as [IAg IA4];
destruct (stk_split bsegs mm 0xe3780 0xe4500 (669504 + 528392) IA4 ltac:(lia)) as [IA5 IA6];
destruct (stk_cb mm 0xe3780 0xe4500 IA5 ltac:(lia)) as [junk3 DST3] end.
clear IA3 IA4 IA5. change (0xe4500 - 0xe3780) with 0xd80 in DST3.
step. call (imemset_spec 0xe3780 0xd80); [reflexivity| reflexivity| reflexivity| lia| lia| lia| exact DST3| assumption|].
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => pose proof (stk_of_cb mm 0xe3780 0xd80 _ POST ltac:(lia)) as IA5 end.
clear POST.
step. zstep. zstep. zstep. step.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
destruct (stk_cb mm 0xe4500 (669504 + 528392) IA6 ltac:(lia)) as [junk4 DST4] end.
clear IA6. change (669504 + 528392 - 0xe4500) with 0x40248 in DST4.
step. call (imemset_spec 0xe4500 0x40248); [reflexivity| reflexivity| reflexivity| lia| lia| lia| exact DST4| assumption|].
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => pose proof (stk_of_cb mm 0xe4500 0x40248 _ POST ltac:(lia)) as IA6 end.
clear POST.
step. step. step. step. if_lit.
zstep. zstep. zstep. step.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
destruct (stk_split bsegs mm 0xe4500 0xe4510 (0xe4500 + 0x40248) IA6 ltac:(lia)) as [IA7 IA8];
destruct (stk_cb mm 0xe4500 0xe4510 IA7 ltac:(lia)) as [junk5 FR5] end.
clear IA6 IA7. change (Z.to_nat (0xe4510 - 0xe4500)) with 16%nat in FR5.
step. step.
step. step.
step. step.
step. zstep.
do 7 step.
release_frame FR ST (bv_unsigned sp).
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
pose proof (stk_of_rw_cells bsegs mm _ _ FR1) as Q0; cbn [cells_size csize Nat.add] in Q0;
pose proof (stk_of_rw_cells bsegs mm _ _ FR5) as Q5; cbn [cells_size csize Nat.add] in Q5;
pose proof (stk_of_cb mm _ _ _ Z1 ltac:(lia)) as Q1 end.
assert (IA : stk bsegs m1 0xa3740 (0xa3740 + 0x81030)).
{ eapply stk_merge3; [exact Q0| exact IA2| | lia| lia].
eapply stk_merge3; [exact IAg| exact IA5| | lia| lia].
eapply stk_merge3; [exact Q5| exact IA8| exact Q1| lia| lia]. }
unfold ia_post. finish.
intros j Hj. unbox MAP. eapply bytes_at_agree; [apply (MAP j); lia|].
intros i Hi. apply MUm. cbn [outside]. rewrite length_le8 in Hi. rewrite wa_unsigned by lia. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
