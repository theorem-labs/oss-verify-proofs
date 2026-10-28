(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac ITree Nodes SysStep Decode.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import MM_syscalls.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImgX F_syscalls.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RunDraw.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.
Section CANSEC1. Context {rc : runConstT}.
Definition rmunmap_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(A L : Z) (errv : word) (lo : Z) (m : word -> option byte) (a : range_ans) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (munmap_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom usegs)
/\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + mmap_len L)]%Z m m'
/\ (match a with RgDone true => True | _ => wmono usegs m m' end)
/\ mem_inv usegs m'
/\ stk usegs m' lo (bv_unsigned sp)
/\ rw_cells usegs m' (errno_addr tp) [C4 (rg_errno a errv)]
/\ match a with RgErr e => (1 <= e <= 4095)%Z | _ => True end.
#[using="Type"] Lemma rmunmap_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
(A L : Z) (errv : word) (lo : Z),
stk usegs m lo (bv_unsigned sp) ->
rw_cells usegs m (errno_addr tp) [C4 errv] ->
mem_inv usegs m ->
a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 L ->
(0 < A)%Z -> (A + mmap_len L <= 2^64)%Z -> (0 < L < 2^64)%Z ->
(lo <= bv_unsigned sp - 48)%Z ->
(errno_addr tp + 4 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= errno_addr tp)%Z ->
(A + mmap_len L <= lo \/ bv_unsigned sp <= A)%Z ->
(A + mmap_len L <= errno_addr tp \/ errno_addr tp + 4 <= A)%Z ->
(164 <= bv_unsigned tp)%Z ->
impl usegs (at_node usegs) (enode (NMunmap A L) (dec_munmap A L))
(epost (rmunmap_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A L errv lo m))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmunmap_entry) fc None m (seg_rom usegs)).
Proof.
intros until lo. intros ST ERR MI -> -> A0 AL L0 LO SEP1 SEP2 SEP3 TP.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + mmap_len L)]%Z m) as MU.
pose proof (wmono_refl usegs m) as WM.
pose proof (mmap_len_ge L) as ML.
unfold rmunmap_entry. apply impl_enode.
Local Ltac2 Set LiaHints.tbl := fun () => "01;0>12428150072.7712428150072.7812969351307.5612969351307.5712975835496.5715400506246.6016792795048.7816792795048.7917221588796.6019006120615.6322284289799.7722284289799.7823230285244.6225076071819.7825076071819.7925566553219.6325566553219.7925566553219.8025566553219.8225966752202.5725968910377.5625968910377.5726494647592.6026494647592.6226494647592.6328807565322.573352608988.60 33680001082.6034290115814.533812382191.70 38806986883.6038806986883.7738806986883.7838806986883.8039282922457.6039939243268.7039939243268.7140190575097.7840190575097.7941564619544.6941564619544.7043059692341.5143653363129.7843653363129.7945221239098.6348513269468.5748519622463.5648519622463.575180980284.63 54618151079.6255104759171.6255104759171.7855104759171.7955104759171.81563227834.62  58988470539.6059020524184.7059020524184.7159453936022.7359453936022.7460505101163.596166287527.60 62623338453.7062631338201.6362900777713.7862900777713.7966417236959.5868611673244.607191075638.60 7191075638.61 7276334966.60 7508761433.62 9281010335.71 9395033064.78 9395033064.79 00000100200600:00>00D00N00X00\00]00^00_00c00d00e00f00g00h00i00m01101501601701801E01K01O01P01T01U01V01W01X01^01b01f01g01h01i01j01n02402:02>02D02J02P02T02U02V02W02X02Y02]02^02_02`02a02b02f02g02k03103803?03L03U03^03g03h03n04204704<FFS2TPS2TPS2TPS4SEP2S4SEP13HspS4SEP13HspS2HBSFFS2HBFFSSSSS2LOS2LOS2LOSSSS2A02AL2L02MLS4SEP3S2HBSS2HeSSSSS4SEP1S2LOS2LOFFSSS2LOS4SEP1S4SEP1S2HBS4SEP1S4SEP1S4SEP1S2HBSSSSSS2HBSSSSSS2ALSS2HeS4SEP1S3Hsp1HS3Hsp1HS2A02AL2L02MLS2LO4SEP2S2LO1H2H0S2LO1H2H0SS4SEP1S2HeS3HspS3Hsp".
carve_frame 32%nat ST.
do 6 step.
step. step.
do 3 step.
step_ecall.
split. { at_node_solve. }
intros rsp ans Hdec. pose proof (dec_munmap_Some _ _ _ _ Hdec) as [ci D]. clear Hdec.
destruct ans as [e|[|]].
- destruct D as [-> He]. sys_nret.
step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
unfold sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
step. step. step. step. step. step. release_frame FR ST (bv_unsigned sp).
unfold rmunmap_post, munmap_ret, rg_errno. finish; lia.
- rewrite D. sys_nret.
step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
unfold sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
step. try rewrite sextw_small by lia. step. step. step. step. step. release_frame FR ST (bv_unsigned sp).
unfold rmunmap_post, munmap_ret, rg_errno. finish; exact I.
- rewrite D. sys_nret.
step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
unfold sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
step. try rewrite sextw_small by lia. step. step. step. step. step. release_frame FR ST (bv_unsigned sp).
unfold rmunmap_post, munmap_ret, rg_errno. finish; exact I.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma rmprotect_args : forall A L, (A mod 4096 = 0)%Z -> (L mod 4096 = 0)%Z -> (0 <= A)%Z -> (0 <= L)%Z -> (A + L + 4096 <= 2^64)%Z ->
Z_to_bv 64 (Z.land 18446744073709547520 (bv_unsigned (Z_to_bv 64 A))) = Z_to_bv 64 A
/\ Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (A + L + 4095))) 18446744073709547520))
- bv_unsigned (Z_to_bv 64 (Z.land 18446744073709547520 (bv_unsigned (Z_to_bv 64 A))))) = Z_to_bv 64 L.
Proof.
intros A L HA HL A0 L0 B. rewrite (Z.land_comm 18446744073709547520).
Local Ltac2 Set LiaHints.tbl := fun () => "0070>17571897768.1021695195569.3028807598860.8 28813880124.1034304160604.105633764624.8  59587396465.8 00000900K00T00]00^00g00kS2A02L01BS2HL2E11H2H02H42H9S2A02L01BS2A02L01BSS2A02L01BS2HA".
rewrite (unsigned_lit A), (unsigned_lit (A + L + 4095)) by lia. rewrite !land_m4096 by lia.
assert (E1 : (A - A mod 4096 = A)%Z) by lia.
assert (E2 : ((A + L + 4095) - (A + L + 4095) mod 4096 = A + L)%Z) by (Z.div_mod_to_equations; lia).
rewrite E1, E2. rewrite !unsigned_lit by lia. split; [reflexivity|]. f_equal. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition rmprotect_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(A L : Z) (errv : word) (lo : Z) (m : word -> option byte) (a : range_ans) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (munmap_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom usegs)
/\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + L)]%Z m m'
/\ wmono usegs m m' /\ mem_inv usegs m'
/\ stk usegs m' lo (bv_unsigned sp)
/\ rw_cells usegs m' (errno_addr tp) [C4 (rg_errno a errv)]
/\ rw_cells usegs m' RPAGE_SIZE [C8 (Z_to_bv 64 4096)]
/\ match a with
| RgErr e => (1 <= e <= 4095)%Z
| RgDone true => rw_cells usegs m' A [CB (Z.to_nat L) (repeat (Z_to_bv 8 0) (Z.to_nat L))]
| RgDone false => True
end.
#[using="Type"] Lemma rmprotect_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
(A L P : Z) (errv : word) (lo : Z),
stk usegs m lo (bv_unsigned sp) ->
rw_cells usegs m (errno_addr tp) [C4 errv] ->
rw_cells usegs m RPAGE_SIZE [C8 (Z_to_bv 64 4096)] ->
mem_inv usegs m ->
a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 L -> a2 = Z_to_bv 64 P ->
(A mod 4096 = 0)%Z -> (L mod 4096 = 0)%Z -> (0 < A)%Z -> (0 < L)%Z -> (A + L + 4096 <= 2^64)%Z -> (0 <= P < 2^64)%Z ->
(lo <= bv_unsigned sp - 32)%Z ->
(errno_addr tp + 4 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= errno_addr tp)%Z ->
(A + L <= lo \/ bv_unsigned sp <= A)%Z ->
(A + L <= errno_addr tp \/ errno_addr tp + 4 <= A)%Z ->
(A + L <= 0x10000 \/ 0x50000 <= A)%Z ->
(0x50000 <= lo)%Z -> (errno_addr tp + 4 <= RPAGE_SIZE \/ RPAGE_SIZE + 8 <= errno_addr tp)%Z ->
(164 <= bv_unsigned tp)%Z ->
impl usegs (at_node usegs) (enode (NMprotect A L P) (dec_mprotect A L))
(epost (rmprotect_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A L errv lo m))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmprotect_entry) fc None m (seg_rom usegs)).
Proof.
intros until lo. intros ST ERR PG MI -> -> -> AA LA A0 L0 AL PR LO SEP1 SEP2 SEP3 SEP4 SLO SEP5 TP.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + L)]%Z m) as MU.
pose proof (wmono_refl usegs m) as WM.
unfold rmprotect_entry, RPAGE_SIZE in *. apply impl_enode.
Local Ltac2 Set LiaHints.tbl := fun () => "0110>10519870008.6012428150072.8612428150072.8812951406312.8712951406312.8912969351307.6512975835496.6512980263190.6715442593460.6715447086794.6515448983337.6515723084706.6715729474111.6515735958492.6516792795048.8716792795048.8920042204689.8720042204689.8920433961190.5921594053147.6822284289799.8622284289799.8823021005697.6724493235832.6924931909275.6025076071819.8725076071819.8926494647592.6628812057224.6629635776758.8729635776758.8930158557427.8931399144472.7831399144472.8032600174396.663525607222.69 3525607222.71 36650778444.893812382191.78 38238797294.663830115332.79 3830115332.81 40097498809.8740097498809.8940190575097.8740190575097.8942358961329.6943059266230.5745221239098.6649677312184.6954164510851.6654164510851.8654164510851.8854494461928.6758988470539.6959020524184.7959020524184.8159377953174.8259377953174.8462623338453.7862631338201.6662900777713.8762900777713.8967081926311.669281010335.79 00000400500600;00@00D00H00L00P00T00X00^00d00j01401>01J01V01W01[01\01]01g01m02102202302402>02D02J02Z02[02\02`02j03403=03A03I03M03Q03W03]03^03_03e03i03m04604704804904B04C04D04E04F04G04K04Q04X04_04`04dS2L0FFS3HspS3HspS2TPS2TPS2TPS2LOS2LOS2LOS4SEP1S4SEP1S4SEP1S4SEP13HspS4SEP13HspS2LO3SLO3HspS2LO3SLO3HspSS2ALFFS2A02L02ALS4SEP3S2A0FFSS2A02L02ALS4SEP5S4SEP5S2L02LO4SEP23HspSSS2HBS2LO3SLO1HS2LO3SLO1HS2L04SEP3S2HeS2LO3SLOS2LOS2LOS4SEP1S4SEP1FFS4SEP4S2LOS2HBS2LO4SEP2SSSS4SEP42HxSSSSSS2HeS4SEP1S3Hsp1HS3Hsp1HSS2He".
carve_frame 16%nat ST.
step. step. step. step.
do 7 step.
destruct (rmprotect_args A L AA LA ltac:(lia) ltac:(lia) AL) as [E1 E2]. rewrite E2, E1.
step. step_ecall.
split. { at_node_solve. }
intros rsp ans Hdec. pose proof (dec_mprotect_Some _ _ _ _ Hdec) as [ci D]. clear Hdec.
rewrite (mmap_len_aligned L LA) in D.
destruct ans as [e|[|]].
- destruct D as [-> He]. sys_nret.
step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
unfold sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
step. step. step. step. release_frame FR ST (bv_unsigned sp).
unfold rmprotect_post, munmap_ret, rg_errno. finish; lia.
- rewrite D.
assert (ROF : forall x : word, (A <= bv_unsigned x < A + L)%Z -> ro_addr usegs x = false) by (intros x Hx; apply ref_ro_addr_false; lia).
sys_nret. lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI end.
step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
unfold sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
step. try rewrite sextw_small by lia. step. step. step. release_frame FR ST (bv_unsigned sp).
unfold rmprotect_post, munmap_ret, rg_errno. finish.
- rewrite D. sys_nret.
step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
unfold sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
step. try rewrite sextw_small by lia. step. step. step. release_frame FR ST (bv_unsigned sp).
unfold rmprotect_post, munmap_ret, rg_errno. finish; exact I.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma land_ones64 y : (0 <= y < 2^64)%Z -> Z.land y 18446744073709551615 = y.
Proof. intros. change 18446744073709551615%Z with (Z.ones 64). Local Ltac2 Set LiaHints.tbl := fun () => "0020=31338480102.335495549846.3000003004S1HS".
rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition rmmap_anon_post (isnone : bool) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(len : Z) (avoid : list (Z * Z)) (errv : word) (lo : Z) (m : word -> option byte) (a : mmap_ans)
: machine_state -> Prop :=
fun ms' =>
match a with
| MmErr e => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom usegs)
/\ munch [(bv_unsigned sp - 80, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
/\ wmono usegs m m' /\ mem_inv usegs m'
/\ stk usegs m' lo (bv_unsigned sp)
/\ rw_cells usegs m' (errno_addr tp) [C4 (Z_to_bv 64 (mmap_fix_errno e))]
/\ (1 <= e <= 4095)%Z
| MmOk x => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m2,
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 x) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None (mmap_raw isnone x len m2) (seg_rom usegs)
/\ munch [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m m2
/\ wmono usegs m m2 /\ mem_inv usegs m2
/\ stk usegs (mmap_raw isnone x len m2) lo (bv_unsigned sp)
/\ rw_cells usegs m2 (errno_addr tp) [C4 errv]
/\ mmap_addr_ok ATOP len avoid x = true
end.
#[using="Type"] Lemma rmmap_anon_spec : forall (isnone : bool) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
(len : Z) (avoid : list (Z * Z)) (errv : word) (lo : Z),
let prot := (if isnone then 0 else 3)%Z in
stk usegs m lo (bv_unsigned sp) ->
rw_cells usegs m (errno_addr tp) [C4 errv] ->
mem_inv usegs m ->
a0 = Z_to_bv 64 0 -> a1 = Z_to_bv 64 len -> a2 = Z_to_bv 64 prot -> a3 = Z_to_bv 64 34 ->
a4 = Z_to_bv 64 (-1) -> a5 = Z_to_bv 64 0 ->
(0 < len <= 2^62)%Z ->
(lo <= bv_unsigned sp - 80)%Z -> (ATOP <= lo)%Z ->
(errno_addr tp + 4 <= bv_unsigned sp - 80 \/ bv_unsigned sp <= errno_addr tp)%Z ->
(164 <= bv_unsigned tp)%Z ->
impl usegs (at_node usegs) (enode (NMmap 0 len prot 34) (if isnone then dec_mmap_none ATOP len avoid else dec_mmap ATOP len avoid))
(epost (rmmap_anon_post isnone ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc len avoid errv lo m))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmmap_entry) fc None m (seg_rom usegs)).
Proof.
intros until lo. intros prot ST ERR MI -> -> -> -> -> -> LEN LO CEIL SEP1 TP.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU1.
pose proof (wmono_refl usegs m) as WM.
atop_facts.
Local Ltac2 Set LiaHints.tbl := fun () => "01U0>11805467289.5811805467289.5911805467289.6011805467289.6111912744615.5912367362435.6012367362435.7712367362435.7812428150072.7512969532418.5413021749692.601527479463.58 15920349859.6816792795048.7617646078182.5019049469500.6121918414723.5921918414723.7521918414723.7722284289799.75239133086.60  24630998586.5825071629079.5825071629079.5925071629079.6025071629079.6125076071819.7625314760359.612685334966.54 27032929881.5927139562509.6730985182006.5831081687356.6132651489978.6033039531175.6133680001082.6136068309337.6036425670404.6836425804963.6436539028409.7636993589379.6136993589379.7536993589379.7837107179452.603812382191.67 39212526441.4539282922457.613945979267.60 3945979267.78 39841462944.5440190575097.7641809558659.5841809558659.7041809558659.7643059350571.4843060403331.6143060403331.7743060403331.7945221239098.6145537716979.6746818470793.4547189242902.7147196384886.7748061821724.6149343544613.6349345641752.6750358273775.5351481786499.6151481786499.7751481786499.7851843525287.6251847587331.5451847587331.6352820344296.7656228262055.60563227834.60  5742912939.62 5744253739.58 57745675194.5958788101849.6159308628179.5259308628304.5259308628304.6459308628433.5259314923118.6360025031335.6162623338453.6762631338201.6162849865985.6262900777713.7663694018620.6165121042193.5267800801447.6067823595993.587010956092.58 7508761433.60 7947824219.59 8583720762.61 9281010335.68 9281348460.53 985337532.59  00000100200300400500600700800900=00A00B00C00R00S00W00X00Y00Z00[00e00i00j00k00l00m00n00o01501;01A01R01V01Z01[01_01e01i01m02302402502602:02>02?02E02F02G02K02L02M02N02O02S02T02U02V02Z02`02a02b02c02o03003103503603703803903=03>03C03D03H03P03d03h03n04204:04N04R04o05005405:05C05J05N05S05T05Z05^05d06806<06@06D06HSSSSSSSSFS2TPS2HBSSS4SEP12He1K3HspSS2HBSSSFS5ATOPR2XCS2HBSSSSFSS4SEP1S4SEP1S2He1KS2LO4CEIL5ATOPR1HS2HBS2HBSS2HBS4SEP1S2LOS2LOS4SEP1SSSS2HBS2HeSS4SEP1SSS2LOFSSSS2LOSSSS2HBS2He1KSSSS2LO4CEIL2XCSSS2HeSSSFS2HeFS3HspSS2HBS2X03HzaS3LEN5ATOPR2X02XC2MLS2HBS4SEP1S2K0S3LEN2K1S3LEN5ATOPR2XC2ML2K1S2K2S3LEN5ATOPR2XA2X02XC2ML3Hza1KSS2HeS4SEP1S4CEIL2XCS3Hsp1HS2HBS3LENSS4SEP1S2HBS4SEP1S3LEN5ATOPR2X02XC2MLS2HBS2HeS2HeS2HB".
assert (PR : (0 <= prot < 4)%Z) by (destruct isnone; subst prot; lia). clearbody prot.
unfold rmmap_entry. apply impl_enode.
carve_frame 64%nat ST.
do 8 step.
step. step. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite ?unsigned_lit in K0 by lia. lia. } clear K0.
step. step. step. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?unsigned_lit in K1 by lia. lia. } clear K1.
step. step. if_cases K2; zify_cond K2. { exfalso. rewrite ?unsigned_lit in K2 by lia. lia. } clear K2.
step. step.
step. step. step_ecall.
split. { at_node_solve. }
intros rsp ans Hdec.
assert (D : exists ci, match ans with
| MmErr e => rsp = efferr_ci ci e /\ (1 <= e <= 4095)%Z
| MmOk a => rsp = (if isnone then mkEffectU (Z_to_bv 64 a) [] [] [(wa a, Z_to_bv 64 (mmap_len len))] [] ci
else mkEffectU (Z_to_bv 64 a) [] [(wa a, Z_to_bv 64 (mmap_len len))] [] [] ci)
/\ mmap_addr_ok ATOP len avoid a = true
end).
{ destruct isnone; [pose proof (dec_mmap_none_Some _ _ _ _ _ Hdec) as [ci D] | pose proof (dec_mmap_Some _ _ _ _ _ Hdec) as [ci D]];
exists ci; destruct ans; exact D. }
clear Hdec. destruct D as [ci D]. destruct ans as [e|x].
- clear MU1. destruct D as [-> He]. sys_nret.
step. step. step.
rewrite unsigned_errno_ret, zb_lxor_ones, Z.lor_0_l by lia.
if_cases K; zify_cond K.
+
step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
unfold sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
do 10 step. release_frame FR ST (bv_unsigned sp).
unfold rmmap_anon_post, mmap_fix_errno. replace (e =? 1)%Z with false by (symmetry; apply Z.eqb_neq; lia).
finish; lia.
+
rewrite ?unsigned_lit in K by lia.
step. step. step. step.
replace (Z_to_bv 64 18446744073709551604) with (errno_ret 12) by (apply bv_eq; reflexivity).
step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
unfold sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
do 10 step. release_frame FR ST (bv_unsigned sp).
unfold rmmap_anon_post, mmap_fix_errno. replace (e =? 1)%Z with true by (symmetry; apply Z.eqb_eq; lia).
finish; lia.
- clear MU. destruct D as [-> Hok]. pose proof (mmap_addr_ok_true _ _ _ _ Hok) as ((XA & X0 & XC) & XAV).
pose proof (mmap_len_ge len) as ML.
lazymatch goal with |- context [nret (MSsvc _ _ _ _ _ _ ?mc _) _] => rename mc into m2 end || idtac.
destruct isnone; sys_nret_raw.
all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
set (m' := mm);
assert (Hza : (0 <= x < 2^64)%Z) by lia; assert (Hzn : (0 <= mmap_len len < 2^64)%Z) by lia;
assert (Hzan : (x + mmap_len len <= 2^64)%Z) by lia
end.
1: pose proof (rw_cells_unmaps_other usegs _ x (mmap_len len) Hza Hzn Hzan _ _ FR ltac:(cbn; lia)) as FR';
pose proof (stk_unmaps_other usegs _ x (mmap_len len) Hza Hzn Hzan _ _ ST ltac:(lia)) as ST'.
2: pose proof (rw_cells_zeros_other usegs _ x (mmap_len len) Hza Hzn Hzan _ _ FR ltac:(cbn; lia)) as FR';
pose proof (stk_zeros usegs _ x (mmap_len len) Hza Hzn Hzan _ _ ST) as ST'.
all: fold m' in FR', ST'; clear FR; rename ST into ST0.
all: step; step; step.
all: rewrite zb_lxor_ones, Z.lor_0_l by (rewrite ?unsigned_lit by lia; lia); rewrite ?unsigned_lit by lia.
all: if_cases K; zify_cond K; rewrite ?land_ones64 in K by lia; [| exfalso; lia].
all: step; step; step; step; if_cases K1; zify_cond K1; [| exfalso; rewrite ?unsigned_lit in K1 by lia; lia]; step.
all: do 9 step; release_frame FR' ST' (bv_unsigned sp); step.
all: apply evt_done; unfold rmmap_anon_post, mmap_raw; cbv iota.
all: do 14 eexists; eexists; split; [subst m'; reflexivity|].
all: split; [exact MU1|]; split; [exact WM|]; split; [exact MI|]; split; [exact ST'|]; split; [exact ERR| exact Hok].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition rmmap_fixed_post {X} (R : X -> word -> bool -> Prop)
(ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(A L : Z) (errv : word) (lo : Z) (m : word -> option byte) (a : X) : machine_state -> Prop :=
fun ms' => exists (r : word) (u : bool) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
R a r u /\
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (sysret_val r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom usegs)
/\ munch [(bv_unsigned sp - 80, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + mmap_len L)]%Z m m'
/\ (u = false -> wmono usegs m m')
/\ mem_inv usegs m'
/\ stk usegs m' lo (bv_unsigned sp)
/\ rw_cells usegs m' (errno_addr tp) [C4 (sysret_errno r errv)].
#[using="Type"] Lemma rmmap_fixed_spec : forall {X} (dec : resp -> option X) (R : X -> word -> bool -> Prop)
ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
(A L P : Z) (errv : word) (lo : Z),
(forall rsp a, dec rsp = Some a -> exists r u, R a r u /\ rstrip rsp = fixed_shape A L r u) ->
stk usegs m lo (bv_unsigned sp) ->
rw_cells usegs m (errno_addr tp) [C4 errv] ->
mem_inv usegs m ->
a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 L -> a2 = Z_to_bv 64 P -> a3 = Z_to_bv 64 50 ->
a4 = Z_to_bv 64 (-1) -> a5 = Z_to_bv 64 0 ->
(0 < A)%Z -> (0 < L <= 2^62)%Z -> (A + mmap_len L < 2^64)%Z -> (0 <= P < 4)%Z ->
(lo <= bv_unsigned sp - 80)%Z ->
(errno_addr tp + 4 <= bv_unsigned sp - 80 \/ bv_unsigned sp <= errno_addr tp)%Z ->
(A + mmap_len L <= lo \/ bv_unsigned sp <= A)%Z ->
(A + mmap_len L <= errno_addr tp \/ errno_addr tp + 4 <= A)%Z ->
(164 <= bv_unsigned tp)%Z ->
impl usegs (at_node usegs) (enode (NMmap A L P 50) dec)
(epost (rmmap_fixed_post R ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A L errv lo m))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmmap_entry) fc None m (seg_rom usegs)).
Proof.
intros until lo. intros DEC ST ERR MI -> -> -> -> -> -> A0 LEN AL PR LO SEP1 SEP2 SEP3 TP.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + mmap_len L)]%Z m) as MU.
pose proof (wmono_refl usegs m) as WM.
pose proof (mmap_len_ge L) as ML.
unfold rmmap_entry. apply impl_enode.
Local Ltac2 Set LiaHints.tbl := fun () => "01Y0>11912744615.6512367362435.6612367362435.8212367362435.8312428150072.8212428150072.8312969532418.6112969532418.6213021749692.661527479463.64 16792795048.8316792795048.8417646078182.5519049469500.6721918414723.6521918414723.8321918414723.8422284289799.8222284289799.8323018884945.5724630998586.6425076071819.8325076071819.8425314760359.6726494647592.6426494647592.6526494647592.6626494647592.672685334966.61 2685334966.62 27032929881.6528807746691.6128807746691.6228814154524.6128916641295.6128916641295.6230985182006.6530985182006.6631081687356.6732651489978.6633039531175.673352608988.64 33680001082.6736068309337.6636425670404.7536425670404.7636539028409.8336539028409.8436993589379.6736993589379.8436993589379.8537107179452.6639282922457.673945979267.66 3945979267.83 3945979267.84 39828213679.7539828213679.7639841462944.6139841462944.6240190575097.8340190575097.8441809558659.6441809558659.8241809558659.8342860264838.6443059692341.5343060403331.6743060403331.8543060403331.8645221239098.6747189242902.7847189242902.7949345641752.7449345641752.7551481786499.6751481786499.8351481786499.8452820344296.8352820344296.8456228262055.66563227834.66  57745675194.6558788101849.6758988470539.6459308628179.5759308628304.5759308628433.5759314923118.6159314923118.6260025031335.6760505101163.6362631338201.6762900777713.8362900777713.8463694018620.6766417236959.6267800801447.6667823595993.646986076828.64 7010956092.64 7508761433.66 8583720762.67 9771863926.68 985337532.65  00000100200300400500600:00>00B00C00M00W00X00\00]00^00_00`00a00f00j00k00l00m00n00o01001101701=01C01Q01_01m01n01o02802A02E02I02J02P02T02Z02^02b02h02n02o03003103503;03<03=03>03?03@03D03H03I03J03K03L03M03S03W03X03Y03Z03^03_03`03a03b03c03d03e03j03o04004404804>04?04C04K04O04U04[04\04`04f04m05405805F05G05M05V05Z05`05d05e05iSSSSFFS2TPS2TPS2HBSS4SEP13HspS4SEP13HspSS2HBSSSFFS3LENS2HBFFSSSSSS4SEP1S4SEP1S4SEP1S2A03LEN2AL2MLS2A03LEN2AL2MLS2A03LEN2AL2MLSSS2LO1H2H0S2LO1H2H0S2HBS2HBSS4SEP3S2HBS4SEP1S2LOS2LOS4SEP1S4SEP1SSSS2HBS4SEP1SSSSSS2LOS2LOFFSSSS4SEP2S2LOSSSS2HBSSSSSSSS3HspS3HspSS2HBS2HBS4SEP1SS2K0S3LEN2K1S2K2S2A01KS2A01KSS2ALS4SEP1S3Hsp1HS3Hsp1HS2HBS2A03LEN2AL2MLSS4SEP1S2LO4SEP2S2HBS4SEP1S2HBSS2HB".
carve_frame 64%nat ST.
do 8 step.
step. step. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite ?unsigned_lit in K0 by lia. lia. } clear K0.
step. step. step. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?unsigned_lit in K1 by lia. lia. } clear K1.
step. step. if_cases K2; zify_cond K2. 2:{ exfalso. rewrite ?unsigned_lit in K2 by lia. lia. } clear K2.
set (z0 := Z_to_bv 64 0). set (zm1 := Z_to_bv 64 (-1)). set (z50 := Z_to_bv 64 50).
set (zA := Z_to_bv 64 A). set (zL := Z_to_bv 64 L). set (zP := Z_to_bv 64 P).
do 6 step. step. step. do 6 step. step.
subst z0 zm1 z50 zA zL zP.
step. step. step_ecall.
split. { at_node_solve. }
intros rsp ans Hdec. destruct (DEC rsp ans Hdec) as (r & u & HR & E). clear Hdec. rewrite <- nret_rstrip, E. clear E.
pose proof (bv_unsigned_in_range 64 r) as RR. change (bv_modulus 64) with (2^64)%Z in RR.
destruct u; unfold fixed_shape; cbv iota.
all: sys_nret.
all: step; step; step.
all: if_cases K; zify_cond K; [| exfalso; apply Z.lor_eq_0_iff in K; lia ].
all: step; call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia |]; rename PC into ST; rename POST into ERR.
all: do 10 step; release_frame FR ST (bv_unsigned sp).
all: unfold rmmap_fixed_post; apply evt_done; exists r; eexists; do 15 eexists; split; [exact HR|]; split; [reflexivity|].
all: split; [ eapply munch_weaken; [|exact MU]; intros y; cbn; lia |].
all: split; [ first [intros; discriminate | intros _; assumption] |].
all: split; [lazymatch goal with H : mem_inv usegs ?mm |- mem_inv usegs ?mm => exact H end|].
all: split; [lazymatch goal with H : stk usegs ?mm ?a ?b |- stk usegs ?mm _ _ => exact H end|].
all: lazymatch goal with H : rw_cells usegs ?mm ?a ?c |- rw_cells usegs ?mm _ _ => exact H end.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Section BRKNODES.
Variables (x1 sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte).
Definition rbrk_regs (a0 : word) : _ :=
mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 (Z_to_bv 64 214) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.
#[using="Type"] Lemma ram_brk0_node :
impl usegs (at_node usegs) (enode (NBrk 0) dec_brk0)
(epost (fun r ms' => ms' = MS (rbrk_regs (Z_to_bv 64 r)) F (Z_to_bv 64 0x15af4) fc None m (seg_rom usegs) /\ (0 <= r < 2^64)%Z))
(MS (rbrk_regs (Z_to_bv 64 0)) F (Z_to_bv 64 0x15af0) fc None m (seg_rom usegs)).
Proof.
unfold rbrk_regs. apply impl_enode. step_ecall. split. { at_node_solve. }
intros rsp r Hdec. apply dec_brk0_Some in Hdec. destruct Hdec as (ci & -> & Hr). sys_nret.
apply evt_done. split; [reflexivity| exact Hr].
Qed.
#[using="Type"] Lemma ram_brk_node_at (pc : Z) :
(pc = 0x15ad8 \/ pc = 0x15b14)%Z -> forall cur req, req <> 0%Z ->
impl usegs (at_node usegs) (enode (NBrk req) (dec_brk cur req))
(epost (fun a ms' => ms' = MS (rbrk_regs (Z_to_bv 64 (brk_res cur req a))) F (Z_to_bv 64 (pc + 4)) fc None (brk_mem m cur req a) (seg_rom usegs)))
(MS (rbrk_regs (Z_to_bv 64 req)) F (Z_to_bv 64 pc) fc None m (seg_rom usegs)).
Proof.
intros Hpc cur req NZ. unfold rbrk_regs.
destruct Hpc as [-> | ->]; (apply impl_enode; step_ecall; split; [at_node_solve|]);
intros rsp a Hdec; apply dec_brk_Some in Hdec; destruct Hdec as [ci Hdec];
(destruct a; rewrite Hdec; unfold eff0_ci, brk_res, brk_mem, zeros_of;
[ destruct (brk_new_pages cur req) as [[lo n]|]; [sys_nret_raw | sys_nret]
| sys_nret ];
apply evt_done; reflexivity).
Qed.
End BRKNODES.
End CANSEC1.
