(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Arr InitMem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import StrFun.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg ABase AQConst.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StepF StrwF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AKit AKit2 AKitQ.
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
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(A, A + n)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' A [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))].
Section IMemset.
Variables (RNG : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : amem).
Hypothesis MI0 : mem_inv asegs m.
Hypothesis AB : bv_unsigned a0 + bv_unsigned a2 < 2^64 /\ 0 < bv_unsigned a2.
Hypothesis RR : rng RNG (bv_unsigned a0) (bv_unsigned a2).
Notation A := (bv_unsigned a0).
Notation n := (bv_unsigned a2).
Notation W := [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z.
Notation POST := (imemset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a4 a5 a6 a7 (bv_unsigned a0) (bv_unsigned a2) m).
Notation ST pc mm x11 x12 x13 :=
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 x11 x12 x13 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).
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
u8arr asegs m1 A bs -> filled (Z_to_bv 8 0) bs Q -> length bs = Z.to_nat n ->
mem_inv asegs m1 -> munch W m m1 -> wmono asegs m m1 ->
(forall j, 0 <= j < i -> Q j) -> 0 <= i < n ->
forall x13, x13 = Z_to_bv 64 (A + i) ->
evtF asegs RNG POST (ST 0x64324 m1 (Z_to_bv 64 0) (Z_to_bv 64 (A + n)) x13).
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
u8arr asegs m1 A bs -> filled (Z_to_bv 8 0) bs Q -> length bs = Z.to_nat n ->
mem_inv asegs m1 -> munch W m m1 -> wmono asegs m m1 ->
(forall j, 0 <= j < i -> Q j) -> 0 <= i < n -> (exists q, i = 16 * q) -> (exists q, n = 16 * q) ->
forall x13, x13 = Z_to_bv 64 (A + i) ->
evtF asegs RNG POST (ST 0x64358 m1 (Z_to_bv 64 0) (Z_to_bv 64 (A + n)) x13).
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
rw_cells asegs m A [CB (Z.to_nat n) junk] ->
evtF asegs RNG POST (ST 0x6430c m (Z_to_bv 64 0) a2 a3).
Proof using AB MI0 RR.
intros junk DST. pose proof MI0 as MI.
pose proof (bv_unsigned_in_range 64 a0) as R0. unfold bv_modulus in R0. cbn in R0.
pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
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
rw_cells asegs m A [CB (Z.to_nat n) junk] ->
mem_inv asegs m ->
rng RNG A n ->
evtF asegs RNG (imemset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a4 a5 a6 a7 A n m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x6430c) fc None m (seg_rom asegs)).
Proof.
intros until junk. intros -> -> -> HA Hn HAn DST MI RR.
pose proof (imemset_body RNG ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m MI) as H.
Local Ltac2 Set LiaHints.tbl := fun () => "0030>28807763462.435619512016.43 61927656618.4300000;00C00NS2HA2Hn3HAnS2Hn3HAnS2HA2Hn3HAn".
rewrite !unsigned_lit in H by lia. apply (H ltac:(lia) RR junk DST).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition ia_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a7 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (m : amem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0xa3680) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0xa3680, 0xa3680 + 0x81030); (0x131f08, 0x131f08 + 4)]%Z m m'
/\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ rw_cells asegs m' 0x131f08 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
/\ stk asegs m' 0xa3680 (0xa3680 + 0x81030)
/\ (forall j, 0 <= j < 32768 -> bytes_at asegs m' (0xa3688 + 8 * j) (le8 (Z_to_bv 64 0))).
#[using="Type"] Lemma internal_allocator_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : amem) (ia : bool) (lo : Z),
stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 ->
mem_inv asegs m ->
rw_cells asegs m AIA_FLAG [C1 (Z_to_bv 8 (if ia then 1 else 0)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
stk asegs m AIA_BASE (AIA_BASE + AIA_SIZE) ->
(ia = true -> forall j, 0 <= j < AIA_MAP1_LEN / 8 -> bytes_at asegs m (AIA_MAP1 + 8 * j) (le8 (Z_to_bv 64 0))) ->
rw_cells asegs m 0x99760 [C8 (Z_to_bv 64 0x131f20)] -> rw_cells asegs m 0x131f20 [C8 (Z_to_bv 64 4096)] ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
evtF asegs RNG (ia_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a7 F fc lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x5e80c) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros ST CEIL LO MI FL IA Z2 PG1 PG2 RIMG RSTK.
unfold AIA_FLAG, AIA_BASE, AIA_SIZE, AIA_MAP1, AIA_MAP1_LEN in *.
word_range sp SPR.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
Local Ltac2 Set LiaHints.tbl := fun () => "03C0?11143995442.69 11804948237.12211805467289.61 11805467289.62 11805467289.63 11805467289.64 12208768790.10812208768790.98 12292222069.11112622122070.11812677422303.11212760837621.11113219133678.64 14118943342.62 14782759150.64 15025058286.61 15610157110.85 16791921141.10016945904050.69 16945904050.83 1707414422.98  17554072693.99 17776320428.61 17776320431.11617776320431.61 1800609155.117 1800609155.62  1800609155.63  18930958230.70 18930958230.81 20270621365.76 20404037910.11120404037910.56 21098180336.12221589365846.11821921109347.11522389541692.61 22437127350.68 22700267513.10122700267513.11322700267513.56 22700267513.57 22700267513.59 22700267513.71 22700267513.85 22883414581.12222883414581.54 23114804310.11823623981241.53 23722017653.69 23722017653.83 23798865741.97 24187486453.69 24187486453.83 24328487285.69 24328487285.83 24638473347.11824638473347.62 24638473347.63 24689793902.63 26161914733.69 26161914733.70 26161914733.83 26437998261.12226494647592.11826494647592.12226494647592.54 26494647592.76 27907200258.54 27907201564.10928417259964.63 30008754969.55 30020848117.99 30816554101.99 31092555110.12231378308326.54 33488551523.11233680001082.64 33910921997.76 34430152252.64 34441176678.12235085513544.70 3529939445.99  35526371414.11835693770006.96 35895277114.12235990850454.86 36027231558.70 36115622446.11736115622447.61 36115622447.62 36157221978.56 36519114324.11836933932602.12237051360698.12237415921909.83 37415921909.84 37654921138.67 37945682572.82 38517088744.1123894052282.122 39110953712.76 39224602138.54 39874974709.11140457739452.62 40836819272.98 40871484270.63 41535431150.61 4270634554.122 43000880110.63 43059266230.52 43987951406.11743987951406.62 43987951406.63 43988483203.11643988483203.61 44512531957.99 44552480493.99 45135277045.99 45221239098.63 45266465884.82 45848756903.61 4621406138.76  46468661564.63 47279694931.54 47346188144.12247346188144.54 48312466362.12248350508273.11848401346248.86 48815604666.76 49109587222.65 49649769127.64 49756215089.12250901757097.11850901757097.12251442136949.69 51442136949.83 51711223320.10851711223320.53 5197023553.122 52105090727.63 53375371158.86 53375371158.97 53726657013.11153767577775.11653767577775.61 53767577775.62 54137460063.84 54243526019.11754243526019.62 55521232486.12255858301882.12256234324469.11256297651176.112563227834.62   56670572338.11157000382702.64 57022093363.54 57495400038.12257622410744.11757745675194.63 57923797554.87 57940983794.11258512233326.63 58684200022.11859251831656.11260692111894.10760858483367.63 61077933805.11161482382924.54 62324116449.11862505509306.76 63235321900.11563235321900.60 63297025046.79 63305555623.62 63385246266.12263385246266.54 63867824918.56 63867824918.70 64245538150.12264297471030.66 64857653178.12264997134979.11864997134979.63 64997134979.64 65088762478.62 65256630714.55 6559611743.100 66260016006.11766260016006.59 6642473454.61  66656729710.62 66680911030.83 66987557365.11167262880580.12267748660341.11167943285742.63 67964909362.99 68059010618.12268059010618.54 68158923058.1107104426426.76  802261998.63   8341085483.112 8442133389.122 8442133389.54  8452716598.108 8583720762.61  9976483528.56  00000100200300400500600700800900:00;00<00E00N00W00`00a00b00h00n00o01001401801<01=01>01?01@01A01J01K01L01M01N01R01V01W01Z01]01a01e02602902<02E02N02O02P02Q02R02S02T02U02V02W02X02Y02Z02c02l02m03603?03@03A03B03C03G03K03O03P03Q03R03S03T03U03Z03[03_03`03a03b03c03d03e03f03g03k03o04304704804904:04;04<04=04A04B04C04D04E04F04J04K04T04]04^04g04k04o05305705805905:05C05D05I05M05N05O05S05T05U05V05W05`05a05b05c05d05e05f05g05h05i05j05k06406506606706806<06@06D06E06F06G06H06I06J06K06P06V06_06`06a06h06m06n06o07807907:07;07<07E07F07G07H07L07P07Q07R07S07T07U07V07W07X07Y07Z07[07\07e07f07g07n08508>08G08H08I08J08K08T08Z08[08\08]08^08g08h08i08j08k090091SSSSSSSSSSFSS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOSFS4CEILS4CEILSSS2LOS2LOS2LOSSSSSS4CEIL2LOSSSSS2HjS2HBSS1HS1HS2HqS2HqS4CEIL2LO2Hj2Hi1HS1HS1HS4CEIL2LOS4CEIL2LOSSSSSSSSSSSSS4CEIL2LOS4CEIL2LOFS4CEIL2LOS4CEIL2LOSSSSS2LOS2LOS2HBSSSSSSS3SPRSS2HBSSSSSSSFS2LOS2LOS2LOS2HjSSSSFSS2HjSSSSSS2HBSS4CEIL2LOS4CEIL2LOSS4CEIL2LOS2LOS2LOS2LOS2LOSSSS4CEIL2LOSS3SPRS2HjSSS2HBSSSSS4CEIL2LOSSSSSSSSSSSS4CEIL2LOSSSSS2LOS2LOS2LOFSSSSFSS3SPRS4CEILS4CEIL2LOSSS2Hj2HiS3SPRSSS4CEIL2LOSSSSS4CEIL2LOSSSS2LOS2LOSSSSSSSSSSSSS4CEIL2LOSFS2Hj2HiS2Hj2HiS4CEIL2LOS4CEIL2LOSSSSS4CEIL2LOS4CEILSSSSS4CEIL2LOSSSSS3SPRS".
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
apply (munch_weaken _ [(bv_unsigned sp - 48, bv_unsigned sp); (0xa3680, 0xa3680 + 0x81030); (0x131f08, 0x131f08 + 4)]%Z) in MU.
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
step. call (imemset_spec 0x124688 40); [reflexivity| reflexivity| reflexivity| lia| lia| lia| exact FR0| assumption|].
rename POST into Z1.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
destruct (stk_split asegs mm 0xa3680 0xa3688 (669312 + 528392) IA ltac:(lia)) as [IA0 IA1] end.
clear IA.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
destruct (stk_cb mm 0xa3680 0xa3688 IA0 ltac:(lia)) as [junk1 FR1] end.
clear IA0. change (Z.to_nat (0xa3688 - 0xa3680)) with 8%nat in FR1.
step.
step. step. step. step.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
destruct (stk_split asegs mm 0xa3688 0xe3688 (669312 + 528392) IA1 ltac:(lia)) as [IA2 IA3] end.
clear IA1.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
destruct (stk_cb mm 0xa3688 0xe3688 IA2 ltac:(lia)) as [junk2 DST2] end.
clear IA2. change (0xe3688 - 0xa3688) with 0x40000 in DST2.
step. call (imemset_spec 0xa3688 0x40000); [reflexivity| reflexivity| reflexivity| lia| lia| lia| exact DST2| assumption|].
rename POST into Z2.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
assert (MAP : forall j, 0 <= j < 32768 -> bytes_at asegs mm (0xa3688 + 8 * j) (le8 (Z_to_bv 64 0)))
by (intros j Hj; apply (cb_zero_le8 _ _ _ _ Z2); lia);
pose proof (stk_of_cb mm 0xa3688 0x40000 _ Z2 ltac:(lia)) as IA2 end.
clear Z2. box MAP. snapshot [(0xe36c0, 0x124688); (0x131f08, 0x131f0c)]%Z MUm WMm.
zstep. zstep. step. step. step.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
destruct (stk_split asegs mm 0xe3688 0xe36c0 (669312 + 528392) IA3 ltac:(lia)) as [IAg IA4];
destruct (stk_split asegs mm 0xe36c0 0xe4440 (669312 + 528392) IA4 ltac:(lia)) as [IA5 IA6];
destruct (stk_cb mm 0xe36c0 0xe4440 IA5 ltac:(lia)) as [junk3 DST3] end.
clear IA3 IA4 IA5. change (0xe4440 - 0xe36c0) with 0xd80 in DST3.
step. call (imemset_spec 0xe36c0 0xd80); [reflexivity| reflexivity| reflexivity| lia| lia| lia| exact DST3| assumption|].
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => pose proof (stk_of_cb mm 0xe36c0 0xd80 _ POST ltac:(lia)) as IA5 end.
clear POST.
step. zstep. zstep. zstep. step.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
destruct (stk_cb mm 0xe4440 (669312 + 528392) IA6 ltac:(lia)) as [junk4 DST4] end.
clear IA6. change (669312 + 528392 - 0xe4440) with 0x40248 in DST4.
step. call (imemset_spec 0xe4440 0x40248); [reflexivity| reflexivity| reflexivity| lia| lia| lia| exact DST4| assumption|].
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => pose proof (stk_of_cb mm 0xe4440 0x40248 _ POST ltac:(lia)) as IA6 end.
clear POST.
step. step. step. step. if_lit.
zstep. zstep. zstep. step.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
destruct (stk_split asegs mm 0xe4440 0xe4450 (0xe4440 + 0x40248) IA6 ltac:(lia)) as [IA7 IA8];
destruct (stk_cb mm 0xe4440 0xe4450 IA7 ltac:(lia)) as [junk5 FR5] end.
clear IA6 IA7. change (Z.to_nat (0xe4450 - 0xe4440)) with 16%nat in FR5.
step. step.
step. step.
step. step.
step. zstep.
do 7 step.
release_frame FR ST (bv_unsigned sp).
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
pose proof (stk_of_rw_cells asegs mm _ _ FR1) as Q0; cbn [cells_size csize Nat.add] in Q0;
pose proof (stk_of_rw_cells asegs mm _ _ FR5) as Q5; cbn [cells_size csize Nat.add] in Q5;
pose proof (stk_of_cb mm _ _ _ Z1 ltac:(lia)) as Q1 end.
assert (IA : stk asegs m1 0xa3680 (0xa3680 + 0x81030)).
{ eapply stk_merge3; [exact Q0| exact IA2| | lia| lia].
eapply stk_merge3; [exact IAg| exact IA5| | lia| lia].
eapply stk_merge3; [exact Q5| exact IA8| exact Q1| lia| lia]. }
unfold ia_post. finish.
intros j Hj. unbox MAP. eapply bytes_at_agree; [apply (MAP j); lia|].
intros i Hi. apply MUm. cbn [outside]. rewrite length_le8 in Hi. rewrite wa_unsigned by lia. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
