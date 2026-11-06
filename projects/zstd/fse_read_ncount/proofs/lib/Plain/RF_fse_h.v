(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas FseHarness.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import Stdio_pure.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseWalkKit.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Plain Require Import PImg StdioFiles.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Plain Require Import RMallocRep RMallocTree RMalloc_iface Harness_iface RDriver_facts.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Plain Require Import RF_fse_iface RF_fse_iface_m RF_fse_h_kit RF_fse_h_B RF_fse_h_D.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Plain Require RMalloc_ifaceP.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim Monad Stdio Malloc Harness Prog.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Plain Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].
Section CANSEC1. Context {rc : runConstT}.
Section FuzzOne.
Hypothesis CREATE : prod_create_stmt.
Hypothesis FMALLOC : fuzz_malloc_stmt.
Hypothesis FREE : rfree_stmt.
Hypothesis PFREE : prod_free_stmt.
Hypothesis U32R : prod_u32r_stmt.
Hypothesis I32R : prod_i32r_stmt.
Hypothesis WBOUND : fse_wbound_stmt.
Hypothesis WRITE : fse_write_stmt.
Hypothesis ISERR : fse_iserror_stmt.
Hypothesis READ : fse_read_stmt.
Definition fh_postB (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PState) (LB : list block) (AB lo D : Z) (payload : list Z) (m : mem)
(r : option bptr) (s' : PState) (ms' : machine_state) : Prop :=
exists (p : bptr) (P : Z) (m1 : mem) (errv1 : word),
r = Some p
/\ phaseB_post gp (Z_to_bv 64 RATP) s8 s9 s10 s11 F fc (bv_unsigned sp + -1632) P D payload lo m1 ms'
/\ RHEAP s' ((p, P, PRODUCER_SIZE) :: LB) m1 /\ rblock_range P PRODUCER_SIZE
/\ rauxv_ok m1 AB /\ rw_cells psegs m1 RERRNO [C4 errv1]
/\ rw_cells psegs m1 (bv_unsigned sp + -72) [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ bytes_at psegs m1 D (map (Z_to_bv 8) payload)
/\ rheap_pres LB (bv_unsigned sp) m m1
/\ ps_so s' = ps_so s.
Definition fh_postD (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PState) (LB : list block) (AB lo : Z) (m : mem) (p : bptr) (P bsz : Z)
(r : option bptr) (s' : PState) (ms' : machine_state) : Prop :=
exists (b : bptr) (BUFF : Z) (m3 : mem) (errv3 : word),
r = Some b
/\ phaseD_post gp (Z_to_bv 64 RATP) s8 s9 s10 s11 F fc (bv_unsigned sp + -1632) P BUFF bsz lo m3 ms'
/\ RHEAP s' ((b, BUFF, bsz) :: (p, P, PRODUCER_SIZE) :: LB) m3 /\ rblock_range BUFF bsz
/\ rauxv_ok m3 AB /\ rw_cells psegs m3 RERRNO [C4 errv3]
/\ rw_cells psegs m3 (bv_unsigned sp + -72) [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ rheap_pres LB (bv_unsigned sp) m m3
/\ ps_so s' = ps_so s.
#[using="CREATE FMALLOC FREE PFREE U32R I32R WBOUND WRITE ISERR READ"] Theorem fuzz_one_proof : fuzz_one_stmt.
Proof.
unfold fuzz_one_stmt. intros until errv. intros HP PAY PAYB PAYR D16 D0 DTOP SZ HC SE AUX SPB ST LOA LOS ERR MI FC TP SP16 A0 A1.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
unfold HARNESS_STACK in LOS. atop_facts.
unfold wz in *. subst tp. rewrite errno_lit in ERR. unfold RERRNO in ERR.
unfold zlength in *.
assert (LENP : zlen (map (Z_to_bv 8) payload) = zlen payload) by (rewrite length_map; reflexivity).
unfold Prog.fuzz_one, Harness.fuzz_one.
apply implM_from_evt.
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl psegs m) as WM.
Local Ltac2 Set LiaHints.tbl := fun () => "02E0?10110401156.21110651190931.11111007500537.17311563874203.16911800475040.13612187165586.10513247374825.21113390583683.21814253206403.21914585332244.16314587527984.21614587527985.19414589624886.75 14589626134.10514589690420.19114589690421.16914591592116.13614878152871.85 16743730337.14017084862631.85 17111776344.13617508180239.21917993200554.76 17995659018.13617997296522.19117997296523.16917997362056.75 18661941992.82 18661941992.83 18661941992.84 18661941992.85 18760472262.1621954476774.112 1958475587.181 19904495118.21119910803004.18320010265080.11220078526778.21121696446342.16422706553108.81 22706661829.85 23875550438.79 23901032282.21623901032283.19423903207776.17525075678749.13926507407396.16826516657987.18027235647879.18127239515170.11228575095975.84 29034408778.77 29149787884.18129153784649.11229803034145.16429803134741.13530516231847.84 3057878485.165 3132468391.82  31723513716.75 32029779012.17732087492205.1813533430915.84  35441788761.17635441788762.21735441788763.19535447803355.1103547740353.211 35958278836.18135962146577.11237097510786.13638455106712.18138748835203.2203886207875.84  39296490819.12439400787283.82 39400787283.83 39400787283.84 39400787283.85 39447646750.16939447646751.19140986768000.82 40986768000.83 40986768000.84 40986768000.85 41119019687.84 41219217343.17341221282481.17743059266230.77 43245452163.21843884027011.84 43998030951.18144565021636.1784496308624.75  45391598317.16445391633369.13545972249987.84 4642516355.219 46986625597.11247169169795.21949705053714.82 49705053714.83 49705053714.84 49705053714.85 49981008014.21149991477434.11449991477436.1835064430759.84  50778961795.83 50818579111.85 52537369151.18152541892506.11253329863184.1635371479421.181 5384388824.112 56721401731.21957416826749.11257420692184.1815822156116.112 5834410225.181 58679658716.16958679658717.19158679724255.75 58681691229.13659698742659.85 6063289124.135 61139363088.16461476207346.21161978189479.83 6295136143.191 63145471107.85 64932245891.22065683752697.11465683752697.13865685865190.13465696140865.11066974396547.85 67541566890.82 67541566890.83 67541566890.84 67541566890.85 67564675252.21668203395203.82 8356419509.194 8838739632.191 8838739633.169 8838805170.75  8840770096.136 9005127794.179 00000=00@00L00M00]00^00k01401=01X02302N02a03403O03j04E04F04d04e04f04o05405A05N05[05`06206D06V06h07;07@07M07V07_07`07i08208G08R08S08\08e08n09C09\09g0:30:70:80:A0:X0:g0;<0;Q0;R0;_0;`0;a0;j0<70<80<A0<J0<S0<T0<]0=90=I0=V0=c0=l0=m0>30>70>;0>?0>C0>P0>]0>n0??0?P0?a0?b0@e0A70A<0AE0AF0AW0A`0Ae0An0B70B80BA0BF0BO0BW0B_0Bg0Bo0C80C90CB0CC0CD0CE0CV0C_0C`0D20D<0DE0DJ0DW0E60Ea0En0F;0F@0FM0FN0F_0G00G10G20G30G40G=0GG0GY0H40HG0HH0HP0HX0H`0Hh0Hi0Hj0Hk0I40I=0I>0IG0IPS3LOS4LBUF2F4S1RS4LBUF2F42DJFS4LBUF2F42F63F11SS3LOS4LBUF2F4S4LBUF2F4S4LBUF2F4S3LOA3LOS3RSP5ATOPR4LBUF2F4S3LOA3LOS3RSP5ATOPR4LBUF2F4S3LOA3LOS3RSP5ATOPR4LBUF2F4S3LOA3LOS3RSP5ATOPRS3LOA3LOS3RSP5ATOPRS3LOA3LOS3RSP5ATOPR4LBUF2F4S3LOA3LOS3RSP5ATOPR4LBUF2F4S3LOA3LOS3RSP5ATOPR4LBUF2F4SS4DTOP3LOA3LOS4LBUF3BR42F43DPASFS4LBUF2F4S3LOAS3LOA4LBUF2F4S3LOA4LBUF2F4S3LOA4LBUF2F4S3LOAS3LOA3LOS5ATOPR2HBS3LOA3LOS5ATOPR2HBS3LOA3LOS5ATOPR2HBS3LOA3LOS5ATOPR2HBS4LBUF2F42F63F112RRS3BR1S4LBUF3BR12F4S4LBUF2F4S4LBUF2F4SS4LBUF2F4S4LBUF2F4S2Hc2D03LOA3RSP5ATOPRS3LOA2H02R4SS4LBUF2F4S4LBUF2F4S4LBUF2F4S3LOA3LOS4LBUF3BR42F4S3LOA3LOS4LBUF3BR42F43BB4S1R4LBUF2F4S2D04LBUF2F4S2D0SS3SPB3LOAS3LOA3LOS5ATOPR4LBUF2F4S3LOA3LOS5ATOPRS3SPB3LOA3LOS4LBUF2F4S3SPB3LOA3LOS4LBUF2F4SS3LOS4LBUF2F4SFS4LBUF2F4S4LBUF2F43BB1SS4LBUF2F4S4LBUF2F4S4LBUF2F4SS4LBUF2F4S2D03RSP4LBUF3BR13BR22F43BB1S2D03RSP3BR13BR2S3LOS4LBUF2F4S3LOS4LBUF2F4S4LBUF2F4SS4LBUFS2HBS2HBS2HBS2HBS3LOS4LBUF2F4S3LOS4LBUF2F4S4DTOP3LOA3LOS2HBS4DTOP3LOA3LOS2HBS4DTOP3LOA3LOS2HBS4DTOP3LOA3LOS2HBSS1R3LOA3LOS4LBUF2F43BB43RSP4LENP3BR13BR52F63F113DPA3BB13BB33BB53BPDS2R12R24LBUF2F42DJS3LOSS4LBUF2F4SS3LOA4LBUF2F43BB4S4LBUF2F4S3LOSS4LBUF2F4S4LBUF2F4SS4LBUF2F4S3LOSS4LBUF2F4S3RSP2HBS3RSP2HBS3RSP2HBS3RSP2HBS4LBUF2F4SS4LBUF2F4SSSS3LOA4LBUF3BR42F4S3LOA3BR4SS4DTOP3LOA4LBUF2F4S4DTOP3LOAS4LBUF2F4S3RSPS3RSP4LBUF2F4S2D03LOA3LOS4SP163RSP5ATOPR3BR1S2D03LOA3LOS4SP163RSP5ATOPR4LBUF3BR12F43BB1S3SPB4LBUF2F4S3SPB4LBUF2F4S3SPBS3SPB4LBUF2F4SS3LOA3LOS4LBUF2F4S3LOA3LOS4LBUF2F4SSFSS4LBUF2F4S2R12R22DJS2R12R24LBUF2F42DJS1R3LOA3LOS4LBUF3BR42F43BR5S1R3LOA3LOS3BR43BR5SS3LOS2HBS3LOS2HBS3LOS2HBS3LOS2HBSSSS4LBUF2F4S4LBUF2F4SS4LBUF2F4S4LBUF2F4".
carve_frame 1632%nat ST.
subst a0 a1. unfold PFUZZ_ENTRY.
zstep. do 9 zstep. zstep.
apply evt_done.
assert (HP1 : RHEAP s LB m0) by (eapply RHEAP_stack_frame; [exact HP| exact MU| exact WM| constructor; [cbn; atop_facts; lia| constructor]]).
assert (AUX1 : rauxv_ok m0 AB) by (eapply rauxv_ok_stack_frame; [exact AUX| exact MU| exact WM| constructor; [cbn; atop_facts; lia| constructor]]).
assert (HPR0 : rheap_pres LB (bv_unsigned sp) m m0).
{ eapply rheap_pres_of_munch; [exact MU| exact WM|]. intros a Ha Hc. cbn. destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [lia| lia|].
pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ _ HP Hb) as (_ & _ & _ & R4 & _). destruct Hr. atop_facts. lia. }
clear HC SE HP AUX.
eapply implM_bind with (Q1 := fh_postB ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB AB lo D payload m).
{ eapply implM_post_evt.
{ unfold prod_create_stmt in CREATE.
eapply CREATE with (lo := lo) (B := AB); try reflexivity; unfold RATP, PROD_CREATE_STACK, FUZZ_MALLOC_STACK, RMALLOC_STACK; rewrite ?unsigned_lit by lia;
first [exact HP1 | exact AUX1 | exact ST | exact MI | lia | change (191552 + -164) with 191388; exact ERR]. }
cbv beta. intros r s' ms1 PO.
destruct PO as (u0 & u1 & u2 & ra0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv1 & -> & MI2 & ST2 & ERR2 & AUX2 & HPR & FAE & SOE & p & P & -> & -> & BR & HP2 & PRC & HEXP).
rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HPR by lia. rewrite errno_lit in ERR2.
replace (ret_pc (Z_to_bv 64 79160)) with (Z_to_bv 64 79160) by (symmetry; rpc).
pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5). unfold PRODUCER_SIZE in BR3, BR4, BR5.
assert (FR2 : rw_cells psegs m2 (bv_unsigned sp + -1632) [CB 1560 (take 1560 (take 1568 (take 1576 (take 1584 (take 1592 (take 1600 (take 1608 (take 1616 (take 1624 junk)))))))));
C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
by (eapply rheap_pres_rw_cells; [exact HPR| exact FR| left; cbn; lia]).
assert (PAY2 : bytes_at psegs m2 D (map (Z_to_bv 8) payload)).
{ eapply rheap_pres_bytes_at; [exact HPR| exact PAY|]. rewrite length_map.
unfold rclient_range in PAYR |- *. destruct PAYR as [R|[R|R]]; [left; lia| right; left; exact R| right; right; exact R]. }
clear FR PAY.
assert (DP : D + zlen payload <= P \/ P + 16 <= D).
{ unfold rclient_range in PAYR. destruct PAYR as [R|[R|(b & Hb & R1 & R2)]]; [lia| lia|].
pose proof (RHEAP_disjoint_head _ _ _ _ _ _ b HP2 Hb) as DJ. unfold PRODUCER_SIZE in DJ. lia. }
apply (proj1 (rw_cells_app _ _ _ [CB 1560 _] _)) in FR2. destruct FR2 as [LOCALS SAVED]. cbn [cells_size csize Nat.add] in SAVED.
replace (bv_unsigned sp + -1632 + Z.of_nat 1560) with (bv_unsigned sp + -72) in SAVED by lia.
eapply evt_mono.
{ eapply (phaseB_proof U32R I32R WBOUND WRITE ISERR);
first [ exact LOCALS | exact PRC | split; [exact PAY2| exact PAYB] | exact ST2 | exact MI2 | exact DP | lia ]. }
cbv beta. intros ms' POB.
exists p, P, m2, errv1. split; [reflexivity|]. split; [exact POB|]. split; [exact HP2|]. split; [exact BR|].
split; [exact AUX2|]. split; [exact ERR2|]. split; [exact SAVED|]. split; [exact PAY2|].
split; [| rewrite SOE; reflexivity].
eapply rheap_pres_trans; [exact HPR0|].
eapply rheap_pres_weaken; [exact HPR| lia| intros b Hb; exact Hb]. }
cbv beta. intros producer sA ms1 (p & P & m1 & errv1 & -> & POB & HPA & BR & AUXA & ERRA & SAVED & PAYA & HPRA & SOA).
clear ERR MI ST FR PAY HP1 AUX1 HPR0 MU WM.
pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5). unfold PRODUCER_SIZE in BR3, BR4, BR5.
destruct POB as (tl & msv & nc & data & dsz & bsz & rem & buf' & junk16 & jtl & rtjunk
& y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y19 & y22 & y23 & y28 & y29 & y30 & y31 & m2
& EA & -> & MUB & WMB & MIB & STB & PRB & FRLOB & NCAB & DATAB & LBUF & FBUF).
assert (AB0 : all_bytes payload) by (apply Forall_all_bytes; exact PAYB).
pose proof (fseA_facts payload (zlen payload) AB0 ltac:(lia)) as FACTS. rewrite EA in FACTS.
destruct FACTS as (F1 & F2 & V & F4 & _ & F6 & _ & _ & F9 & F10 & F11 & F12).
assert (EBS : buff_size payload = bsz).
{ unfold buff_size, fse_bsz, FseNCount.Zlength. rewrite EA. reflexivity. }
rewrite EBS.
assert (DPA : D + zlen payload <= P \/ P + 16 <= D).
{ unfold rclient_range in PAYR. destruct PAYR as [R|[R|(b & Hb & R1 & R2)]]; [lia| lia|].
pose proof (RHEAP_disjoint_head _ _ _ _ _ _ b HPA Hb) as DJ. unfold PRODUCER_SIZE in DJ. lia. }
destruct (fh_transport sA [(p, P, PRODUCER_SIZE)] LB m1 m2 _ AB (bv_unsigned sp + -72) HPA MUB WMB
ltac:(constructor; [right; exists (p, P, PRODUCER_SIZE); split; [left; reflexivity| unfold PRODUCER_SIZE; cbn; lia]
| constructor; [left; cbn; lia| constructor]]) ltac:(lia))
as (HPB & AUXB & ERRB & HPRB).
specialize (AUXB AUXA). specialize (ERRB _ ERRA).
assert (SAVEDB : rw_cells psegs m2 (bv_unsigned sp + -72) [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
{ eapply rw_cells_transport; [exact SAVED| exact MUB| exact WMB|]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
assert (PAYB2 : bytes_at psegs m2 D (map (Z_to_bv 8) payload)).
{ eapply bytes_at_transport; [exact PAYA| exact MUB|]. cbn [disjoint_from]. rewrite length_map. lia. }
clear HPA AUXA ERRA SAVED PAYA.
unfold FSE_MIN_TABLELOG, FSE_MAX_TABLELOG, FseNCount.Zlength in *. cbn [app] in HPB.
eapply implM_bind with (Q1 := fh_postD ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB AB lo m p P bsz).
{ eapply implM_post_evt.
{ unfold fuzz_malloc_stmt, RF_fse_iface_m.PFUZZ_MALLOC in FMALLOC. unfold PFUZZ_MALLOC_B.
eapply FMALLOC with (lo := lo) (B := AB) (n := bsz); try reflexivity; unfold RATP, FUZZ_MALLOC_STACK, RMALLOC_STACK; rewrite ?unsigned_lit by lia;
first [exact HPB | exact AUXB | exact STB | exact MIB | lia | change (191552 + -164) with 191388; exact ERRB]. }
cbv beta. intros r sB ms2 PO.
destruct PO as (u0 & u1 & u2 & ra0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m3 & errv3 & -> & MI3 & ST3 & ERR3 & AUX3 & HPR3 & FAE3 & SOE3 & RR).
rewrite ?unsigned_lit in ST3 by lia. rewrite ?unsigned_lit in HPR3 by lia. rewrite errno_lit in ERR3.
unfold PC_B_EXIT_RA. replace (ret_pc (Z_to_bv 64 79468)) with (Z_to_bv 64 79468) by (symmetry; rpc).
destruct r as [b|]; [| destruct RR as (RR & _); lia].
destruct RR as (BUFF & bjunk & -> & BRB & HP3 & BLK & HEXP). pose proof BRB as (BB1 & BB2 & BB3 & BB4 & BB5).
assert (BPD : BUFF + bsz <= P \/ P + 16 <= BUFF).
{ pose proof (RHEAP_disjoint_head _ _ _ _ _ _ (p, P, PRODUCER_SIZE) HP3 ltac:(left; reflexivity)) as DJ.
cbn [blk_addr blk_size fst snd] in DJ. unfold PRODUCER_SIZE in DJ. lia. }
assert (BDD : BUFF + bsz <= D \/ D + zlen payload <= BUFF).
{ unfold rclient_range in PAYR. destruct PAYR as [R|[R|(b0 & Hb & R1 & R2)]]; [lia| lia|].
pose proof (RHEAP_disjoint_head _ _ _ _ _ _ b0 HP3 ltac:(right; exact Hb)) as DJ. lia. }
assert (CL : forall A n, bv_unsigned sp + -1632 <= A -> rclient_range ((p, P, PRODUCER_SIZE) :: LB) (bv_unsigned sp + -1632) A n) by (intros; left; assumption).
assert (SAVED3 : rw_cells psegs m3 (bv_unsigned sp + -72) [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
by (eapply rheap_pres_rw_cells; [exact HPR3| exact SAVEDB| apply CL; lia]).
assert (FRLO3 : rw_cells psegs m3 (bv_unsigned sp + -1632) [CB 16 junk16; CB 4 jtl; C4 (Z_to_bv 64 255); CB 512 rtjunk])
by (eapply rheap_pres_rw_cells; [exact HPR3| exact FRLOB| apply CL; lia]).
assert (NCA3 : u8arr psegs m3 (bv_unsigned sp + -1632 + OFF_NC) (u16s (map (Z_to_bv 64) nc)))
by (eapply rheap_pres_u8arr; [exact HPR3| exact NCAB| apply CL; unfold OFF_NC; lia]).
assert (DATA3 : u8arr psegs m3 (bv_unsigned sp + -1632 + OFF_DATA) (map (Z_to_bv 8) buf'))
by (eapply rheap_pres_u8arr; [exact HPR3| exact DATAB| apply CL; unfold OFF_DATA; lia]).
assert (PR3 : prod_at m3 P D rem).
{ unfold prod_at in *. eapply rheap_pres_rw_cells; [exact HPR3| exact PRB|]. right. right.
exists (p, P, PRODUCER_SIZE). split; [left; reflexivity|]. cbn. unfold PRODUCER_SIZE. lia. }
assert (PAY3 : bytes_at psegs m3 D (map (Z_to_bv 8) payload)).
{ eapply rheap_pres_bytes_at; [exact HPR3| exact PAYB2|]. rewrite length_map.
unfold rclient_range in PAYR |- *. destruct PAYR as [R|[R|(b0 & Hb & R)]]; [lia| right; left; exact R| right; right].
exists b0. split; [right; exact Hb| exact R]. }
unfold OFF_NC in NCA3. unfold OFF_DATA in DATA3.
eapply evt_mono.
{ eapply (phaseD_proof U32R READ ISERR) with (pl := payload) (lo := lo) (D := D);
first [ exact EA | exact LBUF | exact FBUF | exact BLK | exact FRLO3 | exact NCA3 | exact DATA3 | exact PR3
| split; [exact PAY3| exact PAYB] | exact ST3 | exact MI3 | exact DPA | exact BPD | exact BDD | lia ]. }
cbv beta. intros ms' POD.
exists b, BUFF, m3, errv3. split; [reflexivity|]. split; [exact POD|]. split; [exact HP3|]. split; [exact BRB|].
split; [exact AUX3|]. split; [exact ERR3|]. split; [exact SAVED3|].
split; [| rewrite SOE3; exact SOA].
eapply rheap_pres_trans; [exact HPRA|].
eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact HPRB| lia| intros b0 Hb; exact Hb]|].
eapply rheap_pres_weaken; [exact HPR3| lia| intros b0 Hb; right; exact Hb]. }
cbv beta. intros buff sB ms2 (b & BUFF & m3 & errv3 & -> & POD & HPC & BRB & AUXC & ERRC & SAVEDC & HPRC & SOC).
clear HPB AUXB ERRB HPRB SAVEDB PAYB2 MUB WMB MIB STB PRB FRLOB NCAB DATAB.
pose proof BRB as (BB1 & BB2 & BB3 & BB4 & BB5).
destruct POD as (z5 & z6 & z7 & z9 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z18 & z20 & z21 & z22 & z23 & z28 & z29 & z30 & z31 & m4
& -> & MUD & WMD & MID & STD).
destruct (fh_transport sB [(b, BUFF, bsz); (p, P, PRODUCER_SIZE)] LB m3 m4 _ AB (bv_unsigned sp + -72) HPC MUD WMD
ltac:(constructor; [right; exists (p, P, PRODUCER_SIZE); split; [right; left; reflexivity| unfold PRODUCER_SIZE; cbn; lia]
| constructor; [right; exists (b, BUFF, bsz); split; [left; reflexivity| cbn; lia]
| constructor; [left; cbn; lia| constructor]]]) ltac:(lia))
as (HPD & AUXD & ERRD & HPRD).
specialize (AUXD AUXC). specialize (ERRD _ ERRC). cbn [app] in HPD.
assert (SAVEDD : rw_cells psegs m4 (bv_unsigned sp + -72) [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
{ eapply rw_cells_transport; [exact SAVEDC| exact MUD| exact WMD|]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
clear HPC AUXC ERRC SAVEDC.
destruct (stk_split psegs m4 lo (bv_unsigned sp + -1632) (bv_unsigned sp + -1632 + 1560) STD ltac:(lia)) as [STLO STLOC].
pose proof (RMalloc_ifaceP.RHEAP_blocks_nodup_proof _ _ _ HPD) as ND1.
pose proof (lb_remove_hd b (b, BUFF, bsz) _ eq_refl ND1) as LBR1.
cbn [free_opt]. unfold PFREE_D, PC_D_EXIT_RA.
eapply implM_bind.
{ unfold rfree_stmt, RFREE_SYM in FREE.
eapply FREE with (lo := lo) (B := AB) (A := BUFF) (n := bsz); try reflexivity; unfold RATP, RFREE_STACK; rewrite ?unsigned_lit by lia;
first [exact HPD | left; reflexivity | exact AUXD | exact STLO | exact MID | lia | change (191552 + -164) with 191388; exact ERRD]. }
cbv beta. intros [] sC ms3 PO.
destruct PO as (u0 & u1 & u2 & ra0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & u3 & u4 & u5 & u6 & m5 & -> & MI5 & ST5 & ERR5 & AUX5 & HPR5 & FAE5 & SOE5 & HP5).
rewrite LBR1 in HPR5, HP5.
rewrite ?unsigned_lit in ST5 by lia. rewrite ?unsigned_lit in HPR5 by lia. rewrite errno_lit in ERR5.
replace (ret_pc (Z_to_bv 64 79640)) with (Z_to_bv 64 79640) by (symmetry; rpc).
assert (SAVED5 : rw_cells psegs m5 (bv_unsigned sp + -72) [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
by (eapply rheap_pres_rw_cells; [exact HPR5| exact SAVEDD| left; cbn; lia]).
assert (STLOC5 : stk psegs m5 (bv_unsigned sp + -1632) (bv_unsigned sp + -1632 + 1560))
by (eapply rheap_pres_stk; [exact HPR5| exact STLOC| lia]).
clear SAVEDD STLOC STLO MID ERRD AUXD HPD.
apply implM_from_evt. zstep. zstep. apply evt_done.
pose proof (RMalloc_ifaceP.RHEAP_blocks_nodup_proof _ _ _ HP5) as ND2.
pose proof (lb_remove_hd p (p, P, PRODUCER_SIZE) _ eq_refl ND2) as LBR2.
eapply implM_bind.
{ unfold prod_free_stmt, RF_fse_iface_m.PPROD_FREE in PFREE.
eapply PFREE with (lo := lo) (B := AB) (A := P) (n := PRODUCER_SIZE); try reflexivity; unfold RATP, RFREE_STACK; rewrite ?unsigned_lit by lia;
first [exact HP5 | left; reflexivity | exact AUX5 | exact ST5 | exact MI5 | lia | change (191552 + -164) with 191388; exact ERR5]. }
cbv beta. intros [] sD ms4 PO.
destruct PO as (v0 & v1 & v2 & ra1 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & m6 & -> & MI6 & ST6 & ERR6 & AUX6 & HPR6 & FAE6 & SOE6 & HP6).
rewrite LBR2 in HPR6, HP6.
rewrite ?unsigned_lit in ST6 by lia. rewrite ?unsigned_lit in HPR6 by lia. rewrite errno_lit in ERR6.
replace (ret_pc (Z_to_bv 64 79648)) with (Z_to_bv 64 79648) by (symmetry; rpc).
assert (SAVED6 : rw_cells psegs m6 (bv_unsigned sp + -72) [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
by (eapply rheap_pres_rw_cells; [exact HPR6| exact SAVED5| left; cbn; lia]).
assert (STLOC6 : stk psegs m6 (bv_unsigned sp + -1632) (bv_unsigned sp + -1632 + 1560))
by (eapply rheap_pres_stk; [exact HPR6| exact STLOC5| lia]).
clear SAVED5 STLOC5 MI5 ERR5 AUX5 HP5 ST5.
apply implM_ret.
zstep. do 9 zstep. zstep. zstep.
apply evt_done. unfold fuzz_one_post.
do 14 eexists. exists F, fc, m6, errv3. split; [reflexivity|].
split; [lia|]. split; [exact MI6|]. split; [exact FC|].
split.
{
apply stk_of_rw_cells in SAVED6. cbn [cells_size csize Nat.add] in SAVED6.
replace (bv_unsigned sp + -72 + Z.of_nat 72) with (bv_unsigned sp) in SAVED6 by lia.
replace (bv_unsigned sp + -1632 + 1560) with (bv_unsigned sp + -72) in STLOC6 by lia.
eapply stk_merge; [| exact SAVED6| lia]. eapply stk_merge; [exact ST6| exact STLOC6| lia]. }
split; [rewrite errno_lit; exact ERR6|]. split; [exact AUX6|].
split.
{ eapply rheap_pres_trans; [exact HPRC|].
eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact HPRD| lia| intros b0 Hb; exact Hb]|].
eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact HPR5| lia| intros b0 Hb; right; exact Hb]|].
eapply rheap_pres_weaken; [exact HPR6| lia| intros b0 Hb; exact Hb]. }
split; [exact HP6|]. rewrite SOE6, SOE5. exact SOC.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End FuzzOne.
End CANSEC1.
