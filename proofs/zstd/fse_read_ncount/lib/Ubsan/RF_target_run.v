(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import DrvAgree Startup_kit STRW_tac Amo_tac Keeps F_fmt_fp_lib Printf_fmts.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImgX F_syscalls F_memcpy StdioFiles F_atexit Exit F_printf_iface Stdio_iface Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import MallocBlocks MallocTree MallocHINV Malloc_iface.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_iface Harness_iface RDriver_iface RDriver_facts RDriver_kit RDriver_ctx.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim STree Malloc Monad Stdio Driver Adapter Harness Prog.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].
Section CANSEC1. Context {rcT : runConstT}.
#[using="Type"] Lemma land3_range : forall c, 0 <= c -> 0 <= Z.land c 3 <= 3.
Proof.
intros c Hc. Local Ltac2 Set LiaHints.tbl := fun () => "0040=40825278267.341415985307.346826848796.46746496391.3 000001002005006SSS1HS".
split; [apply Z.land_nonneg; lia|].
change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (Z.ones 2) with 3. pose proof (Z.mod_pos_bound c 4 ltac:(lia)). change (2^2) with 4. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma Forall_skipn' : forall {A} (P : A -> Prop) n (l : list A), Forall P l -> Forall P (skipn n l).
Proof.
intros A P n. induction n as [|n IH]; intros l H; [exact H|]. destruct l as [|x l]; cbn; [constructor|].
inversion H; subst. apply IH. assumption.
Qed.
#[using="Type"] Lemma fuzz_one_leaf0 : forall payload s r s', mleaf (Prog.fuzz_one payload) s r s' -> r = 0.
Proof.
intros payload s r s' H. unfold Prog.fuzz_one, Harness.fuzz_one in H.
repeat (apply mleaf_bind in H; destruct H as (? & ? & _ & H)).
apply mleaf_ret in H. exact (proj1 H).
Qed.
Section RUN.
Hypothesis MALLOC : rmalloc_stmt.
Hypothesis FREE : rfree_stmt.
Hypothesis FUZZ : fuzz_one_stmt.
Hypothesis EMIT : emit_printf_stmt ps_so set_so_ps.
Hypothesis FWXO : fwritex_stdout_stmt.
Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m0 : mem)
(LB : list block) (p : bptr) (A cap L : Z) (content : list Z) (AB lo : Z).
Hypothesis INLB : In (p, A, cap) LB.
Hypothesis FC : Forall (fun c => 0 <= c < 256) content.
Hypothesis LC : zlength content <= cap.
Hypothesis CAP : cap <= 2^26.
Hypothesis L0 : 0 <= L.
Hypothesis L6 : 6 + L <= zlength content.
Hypothesis SPAB : bv_unsigned sp <= AB.
Hypothesis ABB : AB <= 2^47.
Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
Hypothesis CEIL : ATOP <= lo.
Hypothesis LO : lo <= bv_unsigned sp - PTARGET_RUN_STACK.
Notation usp := (bv_unsigned sp).
Notation tpv := (Z_to_bv 64 RATP).
Notation SPF := (Z_to_bv 64 (bv_unsigned sp + -80)).
Definition plen : Z := zlength content - 6 - L.
Definition PAY : Z := A + 6 + L.
Definition payload : list Z := skipn (Z.to_nat (6 + L)) content.
Definition cfg : Z := if 0 <? L then znth content 2 else 0.
Definition calls : Z := 1 + Z.land cfg 3.
Definition LBT (own : option (bptr * Z)) : list block :=
match own with None => LB | Some (q, D) => (q, D, plen) :: LB end.
Definition dptr (own : option (bptr * Z)) : Z := match own with None => PEMPTY | Some (_, D) => D end.
Definition oreg (own : option (bptr * Z)) : Z := match own with None => 0 | Some (_, D) => D end.
Definition omodel (own : option (bptr * Z)) : option bptr := match own with None => None | Some (q, _) => Some q end.
Definition FRAME (m : mem) : Prop :=
exists jb : list byte, rw_cells usegs m (usp + -80) [CB 8 jb; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Definition INV0 (own : option (bptr * Z)) (st : PState) (m : mem) : Prop :=
FRAME m /\ bytes_at usegs m (dptr own) (zbytes payload) /\ harness_cells m /\ stderr_file0 m
/\ (exists errv : word, rw_cells usegs m RERRNO [C4 errv])
/\ mem_inv usegs m /\ stk usegs m lo (usp + -80) /\ rauxv_ok m AB
/\ stdout_file m (ps_so st) /\ pdrv_pres LB usp m0 m /\ atx_state true m.
Definition INV (own : option (bptr * Z)) (st : PState) (m : mem) : Prop := RHEAP st (LBT own) m /\ INV0 own st m.
Notation DST own pc x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 k t3 t4 t5 t6 F fc mm :=
(MS (mkR x1 SPF gp tpv t0 t1 t2 (wz plen) (wz (dptr own)) a0 a1 a2 a3 a4 a5 a6 a7
(wz (oreg own)) x19 (wz PINIT_FLAG) (wz k) (wz 0) (wz (-2)) s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
Definition RUNST (own : option (bptr * Z)) (pc : Z) (k : Z) (st : PState) (ms : machine_state) : Prop :=
exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
ms = DST own pc x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 k t3 t4 t5 t6 F fc m
/\ frm0 fc /\ INV own st m.
#[using="rcT sp cap FC LC CAP L0 L6"] Lemma facts : 0 <= plen /\ plen < 2^26 /\ zlength payload = plen /\ 0 <= cfg < 256 /\ 1 <= calls <= 4 /\ PAY = A + 6 + L.
Proof.
unfold calls, cfg, plen, payload, PAY. unfold zlength in *. rewrite length_skipn.
assert (CF : 0 <= (if 0 <? L then znth content 2 else 0) < 256).
{ Local Ltac2 Set LiaHints.tbl := fun () => "00<0>11421757168.4415570526297.4331248201503.4435218573961.4543149358097.4448569994218.4348569994218.4453850393860.4457013851305.4257013851305.4357857073564.446927967790.44 00000300:00A00G00R00V00Z00]00^00_00c00gS1HS2L02L6S2L02L6S2LT1XS2LC3CAP2L0S2CFS2CFS1HSSS2L6S2CF".
destruct (0 <? L); [|lia]. unfold znth. destruct (Z.ltb_spec 2 0); [lia|].
assert (LT : (Z.to_nat 2 < length content)%nat) by lia.
pose proof (proj1 (Forall_forall _ _) FC _ (nth_In content 0 LT)) as X. cbn beta in X. lia. }
pose proof (land3_range (if 0 <? L then znth content 2 else 0) ltac:(lia)).
repeat split; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rcT LO"] Lemma LO' : lo <= usp - 80 - HARNESS_STACK.
Proof. unfold PTARGET_RUN_STACK in LO. Local Ltac2 Set LiaHints.tbl := fun () => "0010>20922897659.42000004S2LO".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rcT CEIL LO"] Lemma trun_init : forall (Q : machine_state -> Prop) (tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
stk usegs m lo usp -> mem_inv usegs m -> trun_cells0 m -> rw_cells usegs m PNEED_LOCKS [C1 (Z_to_bv 8 0)] ->
(forall (m' : mem) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
FRAME m' -> stk usegs m' lo (usp + -80) -> harness_cells m' -> atx_state true m' ->
munch [(usp - 128, usp); (PINIT_FLAG, PINIT_FLAG + 1); (0x4ef80, 0x4ef84); (0x4ef88, 0x4ef90); (0x4ef98, 0x4efa0); (0x4f098, 0x4f0a0)] m m' ->
wmono usegs m m' -> mem_inv usegs m' ->
evt usegs Q (MS (mkR x1 SPF gp tp x5 x6 x7 a3 a2 (wz 0) x11 x12 x13 x14 x15 x16 x17
a1 a0 (wz PINIT_FLAG) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0x133a0) fc None m' (seg_rom usegs))) ->
evt usegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 PTARGET_RUN) fc None m (seg_rom usegs)).
Proof.
intros until m. intros ST MI TR NL K. pose proof LO' as L'. pose proof CEIL as CEIL'. unfold HARNESS_STACK in CEIL', L'. atop_facts.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
destruct TR as (PI & GFI & GSE & SEP & [(X1 & X2 & X3 & X4 & X5 & X6 & X7) CB]).
unfold PINIT_FLAG, PGOT_FUZZ_INIT, PFUZZ_INIT, PGOT_STDERR, PSTDERR_PTR, PATX, PAEF_INCB, PNEED_LOCKS, wz in *.
pose proof (munch_refl [(usp - 128, usp); (0x2ee30, 0x2ee30 + 1); (0x4ef80, 0x4ef84); (0x4ef88, 0x4ef90); (0x4ef98, 0x4efa0); (0x4f098, 0x4f0a0)] m) as MU.
pose proof (wmono_refl usegs m) as WM.
unfold PTARGET_RUN.
zstep. Local Ltac2 Set LiaHints.tbl := fun () => "02F0?10863132689.10211472836995.92 11658450183.10212619326608.95 1287614481.102 1343986644.102 14152256912.95 14274847920.95 14473342746.80 1668823348.102 18688180200.91 18688180200.92 18688180200.93 18688180200.94 19198118324.10219979465583.10221459337704.91 21459337704.92 21459337704.93 21459337704.94 21609999028.10222105513903.10222226183811.93 23002714856.91 23002714856.92 23002714856.93 23002714856.94 23859210548.10224575440872.91 24575440872.92 24575440872.93 24575440872.94 2459935663.102 2565728400.95  25876235752.91 25876235752.92 25876235752.93 25876235752.94 26058469174.84 26374661236.10226386895023.10326779459055.10326781526324.10227723960707.92 29142331828.10229514161780.10229969828276.10230333463952.95 30360855784.1023051486595.92  31025169140.10233051853800.91 33051853800.92 33051853800.93 33051853800.94 33109901940.10233910686639.10234140309487.10335909988007.92 36708823732.10236730223028.10237011216820.10237107588072.91 37107588072.92 37107588072.93 37107588072.94 39911491956.10240131485072.95 40374333670.85 40690069393.10242148986991.80 42200251523.93 43059266230.83 43154153908.10243626259636.1024391816080.95  44908517748.10244977136295.94 4678877201.102 46887021955.93 47174632628.10247663274663.93 49705053714.91 49705053714.92 49705053714.93 49705053714.94 50169602536.91 50169602536.92 50169602536.93 50169602536.94 50400081012.10250628941955.93 51191632244.95 51872008336.95 51898894772.10252567164907.91 52567164907.92 52567164907.93 52567164907.94 52567164907.95 5300226131.91  5300226131.92  5300226131.93  5300226131.94  53561987728.95 54163155316.10254942994868.10255958408871.93 56185989799.93 57288574440.91 57288574440.92 57288574440.93 57288574440.94 58076620944.95 5896867971.91  59308628179.87 59308628304.1  59308628433.1  59522377383.92 61356224744.91 61356224744.92 61356224744.93 61356224744.94 61994440323.94 62241974760.91 62241974760.92 62241974760.93 62241974760.94 62248247784.91 62248247784.92 62248247784.93 62248247784.94 62611961067.95 6265197590.99  62670790311.93 62900777713.1036539242896.95  67016989713.10267267109685.80 67274770408.91 67274770408.92 67274770408.93 67274770408.94 67965490855.91 68339687665.95 6908899601.102 8079754384.95  8489967087.103 894743207.92   995137972.102  00000D00E00F00G00[00\00]00^00_00`01301F01Y01l01m02=02P02c03603I03J03Z03[03n04A04T04g04h05;05N05a06406D06E06X06k07>07Q07g07h07k07n07o08008108208308408908:08;08N08a09409G09H09X09[09\09]09^09_0:20:E0:X0:k0:l0:m0:n0;B0;O0;P0;T0;U0;V0;W0;X0;Y0;m0;n0;o0<00<80<@0<H0<P0<c0=60=I0=\0=]0=^0=_0=`0=a0=e0=i0=m0>10>20>60>:0>>0>B0>C0>D0>E0>F0>G0>Z0>m0?@0?S0?T0?U0?Y0?]0?a0?b0@50@H0@[0@n0@o0AB0AU0Ah0B;0BN0Ba0C40CG0CW0CX0CY0D30D40DH0DL0D_0E20EE0EX0EY0EZ0En0Eo0F20F30F4S2L'5CEIL'5ATOPR3HspSFSS2L'5CEIL'5ATOPR3HspFSSSSS2L'5CEIL'5ATOPR2HBS2L'5CEIL'5ATOPR2HBS2L'5CEIL'5ATOPR2HBS2L'5CEIL'5ATOPR2HBSS2L'5CEIL'5ATOPRS2L'5CEIL'5ATOPR2HBS2L'5CEIL'5ATOPR2HBS2L'5CEIL'5ATOPR2HBS2L'5CEIL'5ATOPR2HBSS2L'5CEIL'5ATOPRSS2L'5CEIL'5ATOPR2HBS2L'5CEIL'5ATOPR2HBS2L'5CEIL'5ATOPR2HBS2L'5CEIL'5ATOPR2HBSS2L'5CEIL'5ATOPR2HBS2L'5CEIL'5ATOPR2HBS2L'5CEIL'5ATOPR2HBS2L'5CEIL'5ATOPR2HBS2L'5CEIL'5ATOPRSS2L'5CEIL'5ATOPR2HBS2L'5CEIL'5ATOPR2HBS2L'5CEIL'5ATOPR2HBS2L'5CEIL'5ATOPR2HBS2L'5CEIL'5ATOPR3SPR1HSS1HS1HSSSSSSS3HspSSS2L'5CEIL'5ATOPR2HBS2L'5CEIL'5ATOPR2HBS2L'5CEIL'5ATOPR2HBS2L'5CEIL'5ATOPR2HBSS2L'5CEIL'5ATOPRS1HSSSSS2L'5CEIL'5ATOPR2HBS2L'5CEIL'5ATOPR2HBS2L'5CEIL'5ATOPR2HBS2L'5CEIL'5ATOPR2HBSSSS2L'5CEIL'5ATOPR3HspS5CEIL'5ATOPRSS2L'SSSSSS2L'5CEIL'5ATOPR3HspSSSS3SPR2HBS3SPR2HBS3SPR2HBS3SPR2HBS2L'5CEIL'5ATOPR2HBS2L'5CEIL'5ATOPR2HBS2L'5CEIL'5ATOPR2HBS2L'5CEIL'5ATOPR2HBSSSSSS2HBS2HBS2HBS2HBSS2HBS2HBS2HBS2HBSSSSSS2L'5CEIL'5ATOPR2HBS2L'5CEIL'5ATOPR2HBS2L'5CEIL'5ATOPR2HBS2L'5CEIL'5ATOPR2HBSSS2K0S2K1S2K2SS2L'5CEIL'5ATOPR2HBS2L'5CEIL'5ATOPR2HBS2L'5CEIL'5ATOPR2HBS2L'5CEIL'5ATOPR2HBSS2L'5CEIL'5ATOPR2HBS2L'5CEIL'5ATOPR2HBS2L'5CEIL'5ATOPR2HBS2L'5CEIL'5ATOPR2HBS2L'5CEIL'5ATOPR2HBS2L'5CEIL'5ATOPR2HBS2L'5CEIL'5ATOPR2HBS2L'5CEIL'5ATOPR2HBS2L'5CEIL'5ATOPRSSS2L'5CEIL'5ATOPR3SPR3Hsp1HSS2L'5CEIL'5ATOPR3HspS2L'S2L'5CEIL'5ATOPR2HBS2L'5CEIL'5ATOPR2HBS2L'5CEIL'5ATOPR2HBS2L'5CEIL'5ATOPR2HBSSS2L'5CEIL'5ATOPR3HspSS1HSS".
carve_frame 80%nat ST.
do 9 zstep.
do 8 zstep. if_cases K0; zify_cond K0; [| exfalso; lia]. clear K0.
do 5 zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (AX : atx_cells 0 0 0 0 mx) by (exact (conj X1 (conj X2 (conj X3 (conj X4 (conj X5 (conj X6 X7))))))) end.
clear X1 X2 X3 X4 X5 X6 X7.
call_sp patexit_spec;
[ exact ST | exact AX | exact NL | exact MI | reflexivity | lia | lia | lia | ].
zstep. if_cases K1; zify_cond K1; [| exfalso; revert K1; clear; intros K1; rewrite ?unsigned_lit in K1 by lia; lia]. clear K1.
do 3 zstep. if_cases K2; zify_cond K2; [| exfalso; revert K2; clear; intros K2; rewrite ?unsigned_lit in K2 by lia; lia]. clear K2.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => eapply (K mx) end.
- lazymatch goal with H : rw_cells usegs _ (usp + -80) _ |- _ => eexists; exact H end.
- hyp_by_addr.
- unfold harness_cells, PGOT_STDERR, PSTDERR_PTR, wz.
repeat match goal with |- _ /\ _ => split end; assumption.
- unfold atx_state, PEXIT_GUARD, PAEF_INCB. split; [| exact CB].
lazymatch goal with H : atx_cells _ _ _ _ _ |- _ => exact H end.
- exact MU.
- exact WM.
- hyp_by_addr.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="sp p INLB FC LC CAP L0 L6"] Lemma block_facts : forall st own m, RHEAP st (LBT own) m ->
0 < A /\ A + cap <= ATOP /\ (A + cap <= 0x10000 \/ 0x50000 <= A)
/\ match own with None => True | Some (_, D) => 0 < D /\ D mod 16 = 0 /\ D + plen <= ATOP /\ (D + plen <= 0x10000 \/ 0x50000 <= D) end.
Proof.
intros st own m P.
assert (HB : In (p, A, cap) (LBT own)) by (destruct own as [[q D]|]; [right|]; exact INLB).
pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ _ P HB) as (B1 & B2 & B3 & B4 & B5). cbn in B1, B2, B3, B4, B5.
Local Ltac2 Set LiaHints.tbl := fun () => "0040>24946638619.5230994608844.5955478414800.5258273588432.5200000400A00E00IS2B1S2C12C22C42C5S2B4S2B5".
split; [lia|]. split; [lia|]. split; [lia|].
destruct own as [[q D]|]; [| exact I].
pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ _ P ltac:(left; reflexivity)) as (C1 & C2 & C3 & C4 & C5). cbn in C1, C2, C3, C4, C5.
pose proof facts. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma pdrv_pres_of_heap_sub : forall LB' SP' m m',
rheap_pres LB' SP' m m' -> SP' <= usp -> (forall b, In b LB -> In b LB') -> pdrv_pres LB usp m m'.
Proof.
intros LB' SP' m m' HP HS HL. apply pdrv_pres_of_heap. eapply rheap_pres_weaken; [exact HP| exact HS| exact HL].
Qed.
#[using="Type"] Lemma pdrv_pres_of_munch : forall m m' W,
munch W m m' -> wmono usegs m m' ->
Forall (fun iv => (snd iv <= usp /\ ATOP <= fst iv) \/ In iv pstdout_ivs) W ->
(forall b, In b LB -> blk_addr b + blk_size b <= ATOP) ->
pdrv_pres LB usp m m'.
Proof.
intros m m' W MU WM HW HLB a Ha Hc Hx.
destruct (magree_of_munch usegs _ _ _ MU WM a Ha) as [E V]; [| split; [exact E| exact V]].
clear MU WM. induction W as [|iv W IH]; cbn; [exact I|].
inversion HW as [|iv' W' Hiv HW']; subst. destruct iv as [lo' hi']. cbn [fst snd] in Hiv. split; [| apply IH; exact HW'].
destruct Hiv as [[H1 H2]|Hin].
- destruct Hc as [Hc|[Hc|(b & Hb & Hr)]].
+ Local Ltac2 Set LiaHints.tbl := fun () => "0030>14047161197.5714047161197.6019775408805.3 00000@00I00MS2Hc2H12H25ATOPRS2Hr2H21HS2Hr".
lia.
+ atop_facts. lia.
+ pose proof (HLB b Hb). lia.
- intros Hr. apply Hx. clear - Hin Hr. unfold pstdout_ivs, PINIT_FLAG, PAEF_INCB, PATX in Hin |- *. cbn in Hin |- *.
repeat (destruct Hin as [E|Hin]; [injection E; intros <- <-; lia|]). destruct Hin.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma LB_below : forall st own m, RHEAP st (LBT own) m -> forall b, In b LB -> blk_addr b + blk_size b <= ATOP.
Proof.
intros st own m P b Hb.
assert (HB : In b (LBT own)) by (destruct own as [[q D]|]; [right|]; exact Hb).
pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ _ P HB) as (_ & _ & _ & B4 & _). exact B4.
Qed.
#[using="rcT sp"] Lemma atx_state_heap_pres : forall LB' SP' m m' reg, rheap_pres LB' SP' m m' -> atx_state reg m -> atx_state reg m'.
Proof.
intros LB' SP' m m' reg HP. apply (atx_state_agree _ _ _ _ HP). intros a Ha. right; left.
unfold atx_state_addr, atx_addr, PATX, PAEF_INCB, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. Local Ltac2 Set LiaHints.tbl := fun () => "0010>32177090169.50000004S2Ha".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma INV0_after_heap : forall own own' st st' LX SP' m m' (errv' : word),
INV0 own st m ->
rheap_pres LX SP' m m' -> SP' <= usp + -80 -> (forall b, In b LB -> In b LX) ->
bytes_at usegs m' (dptr own') (zbytes payload) -> ps_so st' = ps_so st ->
rw_cells usegs m' RERRNO [C4 errv'] -> mem_inv usegs m' -> stk usegs m' lo (usp + -80) -> rauxv_ok m' AB ->
INV0 own' st' m'.
Proof.
intros own own' st st' LX SP' m m' errv' (FR & PB & HC & SE & _ & _ & _ & _ & SO & DP0 & AX) HP HS HL PB' ESO ERR' MI' ST' AUX'.
assert (HPW : rheap_pres LB (usp + -80) m m') by (eapply rheap_pres_weaken; [exact HP| exact HS| exact HL]).
split. { destruct FR as [jb FR]. exists jb. Local Ltac2 Set LiaHints.tbl := fun () => "0040>32972821725.6939373268606.6948333895022.689567985117.69 000001002006007SSS2HSS".
eapply rheap_pres_rw_cells; [exact HPW| exact FR| left; cbn; lia]. }
split; [exact PB'|].
split.
{ destruct HC as (C5 & C6). unfold harness_cells, PGOT_STDERR, PSTDERR_PTR in *.
Ltac hp HPW C := eapply rheap_pres_rw_cells; [exact HPW| exact C| right; left; cbn; unfold RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP; lia].
split; [hp HPW C5| hp HPW C6]. }
split; [eapply stderr_file0_heap_pres; [exact HPW| exact SE]|].
split; [exists errv'; exact ERR'|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AUX'|]. split.
{ rewrite ESO. eapply stdout_file_heap_pres; [exact HPW| exact SO]. }
split; [| eapply atx_state_heap_pres; [exact HPW| exact AX]].
eapply pdrv_pres_trans; [exact DP0|]. eapply pdrv_pres_of_heap_sub; [exact HP| lia| exact HL].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma unsigned_wz_mod32 : forall r, bv_unsigned (wz r) mod 2^32 = r mod 2^32.
Proof.
intros r. unfold wz. rewrite unsigned_lit_wrap. apply Z.mod_mod_divide. exists (2^32). reflexivity.
Qed.
#[using="FUZZ EMIT FWXO p A cap INLB FC LC CAP L0 L6 SPAB ABB SP16 CEIL LO"] Lemma call_body : forall own k st ms {B} (K : Z -> @M PState B) (Q : B -> PState -> machine_state -> Prop),
1 <= k <= 4 -> match own with None => plen = 0 | Some _ => True end -> RUNST own 0x13410 k st ms ->
(forall rc' st' ms', RUNST own (if k =? 1 then 0x13448 else 0x13410) (k - 1) st' ms' -> rc' = 0 -> implM usegs (K rc') st' Q ms') ->
implM usegs (rc' <- Prog.fuzz_one payload ;; io_emit Prog.io rc' ;;; K rc') st Q ms.
Proof.
intros own k st ms B K Q HK OWNZ R HKONT.
destruct R as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & x19 & t3 & t4 & t5 & t6 & F & fc & m & -> & FRM & [P IV]).
pose proof IV as ([jb FR] & PB & [C5 C6] & SE & [errv ERR] & MI & ST & AUX & SO & DP & [(X1 & X2 & X3 & X4 & X5 & X6 & X7) CB]).
pose proof facts as (PL0 & PLM & PLEN & CFG & CALLS & EPAY).
pose proof LO' as L'. pose proof CEIL as CEIL'. unfold HARNESS_STACK in CEIL', L'. atop_facts.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
pose proof (block_facts _ _ _ P) as (BA1 & BA2 & BA3 & BOWN). atop_facts.
unfold PAEF_INCB in CB. unfold PGOT_STDERR, PSTDERR_PTR, wz in C5, C6. unfold RERRNO in ERR.
assert (PBX : True -> bytes_at usegs m (dptr own) (zbytes payload)) by (intros _; exact PB). clear PB IV.
assert (PBR : forall a, dptr own <= a < dptr own + Z.of_nat (length (zbytes payload)) -> outside [(0x2ee34, 0x2ee34 + 1)] a).
{ intros a Ha. rewrite zbytes_length in Ha. unfold zlength in PLEN. cbn. split; [| exact I].
Local Ltac2 Set LiaHints.tbl := fun () => "01Y0?10336209457.12310336209457.1471050254366.109 12124778447.14212298808528.12312298808528.14714230188678.10816697149189.13717309503357.14218459507889.16919986019069.14222345849738.16222706553362.11522706553362.11622706553362.14022706553362.14125892527824.12325892527824.14726056220545.13726056564531.13426056564533.10926058674958.16227241612289.11027788561039.14228425024555.12328425024555.14728573888615.16528816573020.16628816573020.16728816573020.16829085982332.10829086178902.13730062837487.13430432100048.12330432100048.14731689296564.12331689296564.14731786888109.16532097195584.11532097195590.14032976934013.14133020518333.14233760743445.16434202404304.12334202404304.14735583023695.14235927034076.10935995240365.10836099321040.12336099321040.14736990500046.10836990500046.11039360456299.13739360734942.14140483674320.12340483674320.14740520264471.1654160785935.142 416194530.163  42151167042.13442697309208.13443279754203.16445625190034.11045625255608.139460611069.142  47289466576.12347289466576.14747310987279.14149269523343.14249765102479.14249855819069.14250160673408.16551399439631.14252992740247.16553462744784.12353462744784.14758127908239.14259116857748.16359308630497.1  61322386173.10961486512753.13461660565565.14261666808890.14161666808892.11662073606277.11062485698514.16264653469355.16366151427842.19 66464852176.12366464852176.14767186921424.12367186921424.1476933892746.141 7093500157.142 7568928067.123 7568928067.147 7695596239.142 818370139.164  8589980431.141 8733072078.110 8828204805.137 8828385201.109 9572097405.141 9656894205.142 9770003069.142 00000100200600700800900@00A00B00F00G00H00L00P00T00X00Y00Z00n01B01V01j02002102A02Q02d03=03A03_03`03f04004104204304404:04O04d04e04f04l04m04n04o05505605705805<05N05O05P05Q05R05g05h05o06<06@06A06G06M06N06O06P06Q06R06S06T06f06g07<07=07>07?07F07J07X07Y07Z07[07\08108508908G08H08I08J08K08L08M08N08O08P08Q08R08X08Y08Z08[08\08]SSS2L'FSSS5ATOPRSSS2HKSSS2HaS2HaS2HaS2HaSSS2L'5CEIL'5ATOPR3SPRS2L'5CEIL'5ATOPR3SPRS2L'5CEIL'5ATOPR3SPRS2L'5CEIL'5ATOPR3SPRS4BOWNFS2L'5CEIL'5ATOPRS2L'5CEIL'5ATOPRS2L'5CEIL'5ATOPR2HaS4PLEN5CEIL'5ATOPR3SPR2HaS2HaS4PLEN5CEIL'5ATOPR3SPR4BOWN2HaSS4PLENS4SPAB3ABBSSSSS4CEILS4SPAB2L'5CEIL'5ATOPRS4SPAB2L'5CEIL'5ATOPRSSS4CEILSSFS4SPABSSSS2HaS4PLEN3SPR4BOWN2HaSSSSS4SPAB2L'5CEIL'5ATOPRFS2HK2KKS5CEIL'5ATOPRS2L'SS4PLENS4PLENSSSFFFFS4SPAB5CEIL'5ATOPRFS4SPAB2L'5CEIL'5ATOPRSSFS2HK2KKS2KBS3PLM4PLEN3SPRSSSSS4PLEN5ATOPR3SPR4BOWNS2HKS2HKS4SP161H2H02H4SSSSSSSSFSFS4BOWNSSSSS".
destruct own as [[q D]|]; cbn [dptr] in Ha |- *; [atop_facts; lia| unfold PEMPTY in *; lia]. }
unfold PINIT_FLAG, wz. unfold implM. iprefix.
pose proof (munch_refl [(0x2ee34, 0x2ee34 + 1)] m) as MU. pose proof (wmono_refl usegs m) as WM.
zstep. zstep. zstep. zstep. zstep. apply evt_done.
lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm st Q msx) end.
lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
lazymatch goal with MU1 : munch _ m mx, WM1 : wmono usegs m mx |- _ =>
pose proof (magree_of_munch usegs _ _ _ MU1 WM1) as AG1;
assert (PB1 : bytes_at usegs mx (dptr own) (zbytes payload)) by (eapply bytes_at_magree; [exact AG1| exact (PBX I)| intros a Ha; apply PBR; exact Ha]);
assert (SE1 : stderr_file0 mx) by (eapply (stderr_file0_agree _ _ _ AG1); [| exact SE]; intros a Ha; cbn; unfold stderr_addr in Ha; lia);
assert (SO1 : stdout_file mx (ps_so st)) by (eapply (stdout_file_agree _ _ _ _ AG1); [| exact SO]; intros a Ha; cbn; unfold stdout_addr in Ha; lia);
assert (AUX1 : rauxv_ok mx AB) by (eapply rauxv_ok_frame; [exact AUX| exact MU1| exact WM1|]; unfold RAUXV_CELL, RLIBC in *; constructor; [cbn [fst snd]; lia| constructor]);
assert (P1 : RHEAP st (LBT own) mx) by (eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact P| exact MU1| exact WM1|];
constructor; [right; left; cbn [fst snd]; unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP; lia| constructor]);
assert (DP1 : pdrv_pres LB usp m0 mx) by (eapply pdrv_pres_trans; [exact DP|]; eapply pdrv_pres_of_munch; [exact MU1| exact WM1| | apply (LB_below _ _ _ P)];
constructor; [right; cbn; right; right; right; left; reflexivity| constructor]);
clear MU1 WM1 AG1 SO SE AUX P DP PBX
end end.
eapply implM_bind.
{
eapply implM_leaves.
eapply FUZZ with (lo := lo) (AB := AB) (LB := LBT own) (D := dptr own) (payload := payload) (errv := errv);
rewrite ?(unsigned_lit (usp + -80)) by lia.
- exact P1.
- exact PB1.
- unfold payload. apply Forall_skipn'. exact FC.
- destruct own as [[q D]|]; cbn [dptr LBT].
+ right; right. exists (q, D, plen). split; [left; reflexivity|]. cbn. lia.
+ right; left. unfold PEMPTY, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP. rewrite PLEN.
rewrite OWNZ. lia.
- destruct own as [[q D]|]; cbn [dptr]; [lia| reflexivity].
- destruct own as [[q D]|]; cbn [dptr]; [lia| unfold PEMPTY; lia].
- destruct own as [[q D]|]; cbn [dptr]; [atop_facts; lia| unfold PEMPTY; rewrite PLEN, OWNZ; lia].
- lia.
- unfold harness_cells, PGOT_STDERR, PSTDERR_PTR, wz. split; hyp_by_addr.
- exact SE1.
- exact AUX1.
- lia.
- hyp_by_addr.
- exact CEIL.
- unfold HARNESS_STACK. lia.
- unfold RATP, RERRNO. rewrite (unsigned_lit 192304) by lia. change (192304 + -164) with 192140. exact ERR.
- hyp_by_addr.
- exact FRM.
- reflexivity.
- clear -SP16 SPR L'. Z.div_mod_to_equations. lia.
- reflexivity.
- rewrite PLEN. reflexivity. }
cbv beta. intros r st1 ms1 [PO LEAF].
apply fuzz_one_leaf0 in LEAF. subst r.
destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & mF & errv1
& -> & RR & MI1 & FRM1 & ST1 & ERR1 & AUX2 & HPR & P2 & SOE).
rewrite ?(unsigned_lit (usp + -80)) in ST1 by lia. rewrite ?(unsigned_lit (usp + -80)) in HPR by lia.
unfold RATP in ERR1. rewrite ?(unsigned_lit 192304) in ERR1 by lia. change (192304 + -164) with 192140 in ERR1.
replace (ret_pc (Z_to_bv 64 0x13424)) with (Z_to_bv 64 0x13424) by (symmetry; rpc).
assert (HPW : rheap_pres LB (usp + -80) mF mF -> True) by (intros; exact I). clear HPW.
lazymatch type of HPR with rheap_pres _ _ ?ma _ =>
assert (HPW : rheap_pres LB (usp + -80) ma mF) by (eapply rheap_pres_weaken; [exact HPR| lia| intros b Hb; destruct own as [[q D]|]; [right|]; exact Hb]);
assert (PB2 : bytes_at usegs mF (dptr own) (zbytes payload))
by (eapply rheap_pres_bytes_at; [exact HPR| exact PB1|];
destruct own as [[q D]|]; cbn [dptr LBT];
[ right; right; exists (q, D, plen); split; [left; reflexivity|]; cbn; rewrite zbytes_length; unfold zlength in PLEN; lia
| right; left; unfold PEMPTY, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP; rewrite zbytes_length; unfold zlength in PLEN; rewrite OWNZ in PLEN; lia]);
assert (SO2 : stdout_file mF (ps_so st1)) by (rewrite SOE; eapply stdout_file_heap_pres; [exact HPW| exact SO1]);
assert (SE2 : stderr_file0 mF) by (eapply stderr_file0_heap_pres; [exact HPW| exact SE1]);
assert (DP2 : pdrv_pres LB usp m0 mF) by (eapply pdrv_pres_trans; [exact DP1|]; eapply pdrv_pres_of_heap_sub; [exact HPR| lia| intros b Hb; destruct own as [[q D]|]; [right|]; exact Hb]);
repeat match goal with H : rw_cells usegs ma ?A ?cs |- _ =>
first [ apply (rheap_pres_rw_cells _ _ _ _ _ _ HPW) in H; [| first [left; cbn; lia | right; left; cbn; unfold RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP; lia]]
| clear H ] end;
clear HPW HPR PB1 SO1 SE1 AUX1 P1 DP1
end.
unfold implM. iprefix.
pose proof (munch_refl [(0x2ee34, 0x2ee34 + 1)] mF) as MU. pose proof (wmono_refl usegs mF) as WM.
assert (PBX : True -> bytes_at usegs mF (dptr own) (zbytes payload)) by (intros _; exact PB2). clear PB2.
zstep. zstep. zstep. zstep. apply evt_done.
lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm st1 Q msx) end.
lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
lazymatch goal with MU2 : munch _ mF mx, WM2 : wmono usegs mF mx |- _ =>
pose proof (magree_of_munch usegs _ _ _ MU2 WM2) as AG2;
assert (PB3 : bytes_at usegs mx (dptr own) (zbytes payload)) by (eapply bytes_at_magree; [exact AG2| exact (PBX I)| intros a Ha; apply PBR; exact Ha]);
assert (SE3 : stderr_file0 mx) by (eapply (stderr_file0_agree _ _ _ AG2); [| exact SE2]; intros a Ha; cbn; unfold stderr_addr in Ha; lia);
assert (SO3 : stdout_file mx (ps_so st1)) by (eapply (stdout_file_agree _ _ _ _ AG2); [| exact SO2]; intros a Ha; cbn; unfold stdout_addr in Ha; lia);
assert (AUX3 : rauxv_ok mx AB) by (eapply rauxv_ok_frame; [exact AUX2| exact MU2| exact WM2|]; unfold RAUXV_CELL, RLIBC in *; constructor; [cbn [fst snd]; lia| constructor]);
assert (P3 : RHEAP st1 (LBT own) mx) by (eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact P2| exact MU2| exact WM2|];
constructor; [right; left; cbn [fst snd]; unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP; lia| constructor]);
assert (DP3 : pdrv_pres LB usp m0 mx) by (eapply pdrv_pres_trans; [exact DP2|]; eapply pdrv_pres_of_munch; [exact MU2| exact WM2| | apply (LB_below _ _ _ P2)];
constructor; [right; cbn; right; right; right; left; reflexivity| constructor]);
clear MU2 WM2 AG2 SO2 SE2 AUX2 P2 DP2 PBX
end end.
eapply implM_bind.
{ eapply implM_keeps with (f := ps_heap); [| apply s_emit_heap].
unfold io_emit, Prog.io, io_S.
eapply EMIT with (lo := lo) (canary := CAN) (v := 0);
rewrite ?(unsigned_lit (usp + -80)) by lia.
- intros; reflexivity.
- intros; reflexivity.
- exact FWXO.
- exact SO3.
- lia.
- apply unsigned_wz_mod32.
- hyp_by_addr.
- unfold EMIT_DEPTH, HARNESS_STACK in *. lia.
- unfold GLOBALS_TOP. lia.
- lia.
- apply (RHEAP_ssp _ _ _ P3).
- hyp_by_addr.
- exact FRM1. }
cbv beta. intros [] st2 ms2 [PO EH].
destruct PO as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & F2 & fc2 & mE & -> & MUc & WMc & MI2 & FRM2 & FEQ & ST2 & SO4 & SSP2).
rewrite ?(unsigned_lit (usp + -80)) in MUc by lia. rewrite ?(unsigned_lit (usp + -80)) in ST2 by lia.
replace (ret_pc (Z_to_bv 64 0x13434)) with (Z_to_bv 64 0x13434) by (symmetry; rpc).
pose proof (magree_of_munch usegs _ _ _ MUc WMc) as AG.
assert (OUT : forall a, (usp + -80 <= a \/ (a < lo /\ (a < 0x10000 \/ 0x50000 <= a)) \/ (0x10000 <= a < 0x50000 /\ ~ (RSTDOUT <= a < RSTDOUT + 232) /\ ~ (RSTDOUT_BUF <= a < RSTDOUT_BUF + 1024)))
-> (fun a0 : Z => outside [(lo, usp + -80); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)] a0) a).
{ intros a Ha. cbn. lia. }
lazymatch type of MUc with munch _ ?mb mE =>
assert (P4 : RHEAP st2 (LBT own) mE);
[ eapply RHEAP_ext with (s := st1); [| | ]; cycle 1;
[ unfold ps_heap in EH; congruence
| unfold ps_heap in EH; congruence
| eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact P3| exact MUc| exact WMc|];
constructor; [left; cbn [fst snd]; atop_facts; lia|];
constructor; [right; left; cbn [fst snd]; unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP; lia|];
constructor; [right; left; cbn [fst snd]; unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP; lia| constructor] ]
|];
assert (IV2 : INV0 own st2 mE);
[ split; [ exists jb; eapply rw_cells_magree; [exact AG| hyp_by_addr| intros a Ha; apply OUT; cbn in Ha; lia] |];
split; [ eapply bytes_at_magree; [exact AG| exact PB3|]; intros a Ha; apply OUT; rewrite zbytes_length in Ha; unfold zlength in PLEN;
destruct own as [[q D]|]; cbn [dptr] in Ha |- *; [atop_facts; lia| unfold PEMPTY in *; rewrite OWNZ in PLEN; lia] |];
split; [ unfold harness_cells, PGOT_STDERR, PSTDERR_PTR, wz; split;
(eapply rw_cells_magree; [exact AG| hyp_by_addr| intros a Ha; apply OUT; cbn in Ha; lia]) |];
split; [ eapply (stderr_file0_agree _ _ _ AG); [| exact SE3]; intros a Ha; apply OUT; unfold stderr_addr in Ha; lia |];
split; [ exists errv1; eapply rw_cells_magree; [exact AG| unfold RERRNO; hyp_by_addr| intros a Ha; apply OUT; unfold RERRNO in Ha; cbn in Ha; lia] |];
split; [exact MI2|]; split; [exact ST2|];
split; [ eapply rauxv_ok_frame; [exact AUX3| exact MUc| exact WMc|]; unfold RAUXV_CELL, RLIBC in *;
constructor; [cbn [fst snd]; lia|]; constructor; [cbn [fst snd]; lia|]; constructor; [cbn [fst snd]; lia| constructor] |];
split; [exact SO4|];
split; [ eapply pdrv_pres_trans; [exact DP3|]; eapply pdrv_pres_of_munch; [exact MUc| exact WMc| | apply (LB_below _ _ _ P3)];
constructor; [left; cbn [fst snd]; lia|]; constructor; [right; cbn; left; reflexivity|]; constructor; [right; cbn; right; left; reflexivity| constructor] |];
unfold atx_state, atx_cells, PAEF_INCB; cbn [negb];
repeat match goal with |- _ /\ _ => split end;
(eapply rw_cells_magree; [exact AG| hyp_by_addr| intros a Ha; apply OUT; cbn in Ha; lia])
|] end.
clear AG OUT MUc WMc.
eapply implM_evt; [| intros ms' H; exact (HKONT _ _ _ H eq_refl)].
zstep. zstep. if_cases KB; zify_cond KB; [| exfalso; revert KB; clear; intros KB; rewrite ?unsigned_lit in KB by lia; cbn in KB; lia]. clear KB.
zstep. rewrite (swrap32_small (k + -1)) by lia. zstep. if_cases KK; zify_cond KK.
- replace (k =? 1) with false by (symmetry; apply Z.eqb_neq; lia).
apply evt_done. unfold RUNST. do 17 eexists. exists F2, fc2, mE.
split; [reflexivity|]. split; [exact FRM2|]. split; [exact P4| exact IV2].
- replace (k =? 1) with true by (symmetry; apply Z.eqb_eq; lia).
apply evt_done. unfold RUNST. do 17 eexists. exists F2, fc2, mE.
split; [reflexivity|]. split; [exact FRM2|]. split; [exact P4| exact IV2].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="FUZZ EMIT FWXO p A cap INLB FC LC CAP L0 L6 SPAB ABB SP16 CEIL LO"] Lemma calls_loop : forall (n : nat) own rc st ms,
(1 <= n <= 4)%nat -> match own with None => plen = 0 | Some _ => True end ->
RUNST own 0x13410 (Z.of_nat n) st ms ->
implM usegs (run_calls Prog.fuzz_one (io_emit Prog.io) n payload rc) st (fun rc' st' ms' => RUNST own 0x13448 0 st' ms' /\ rc' = 0) ms.
Proof.
Local Ltac2 Set LiaHints.tbl := fun () => "0060>20583756971.5442350912689.4950406667298.5451940350153.5163879219468.5365820017904.5400000400800<00@00A00ES2HNS2HNS2HNS2HNSS2HN".
induction n as [|n IH]; intros own rc st ms HN OWNZ R; [lia|].
cbn [run_calls].
eapply (call_body own (Z.of_nat (S n)) st ms (fun rc' => run_calls Prog.fuzz_one (io_emit Prog.io) n payload rc')); [lia| exact OWNZ| exact R|].
intros rc' st' ms' R' ->. destruct n as [|n'].
- cbn [run_calls]. replace (Z.of_nat 1 =? 1) with true in R' by reflexivity. apply implM_ret. apply evt_done.
replace (Z.of_nat 1 - 1) with 0 in R' by lia. split; [exact R'| reflexivity].
- replace (Z.of_nat (S (S n')) =? 1) with false in R' by (symmetry; apply Z.eqb_neq; lia).
apply (IH own 0); [lia| exact OWNZ|]. replace (Z.of_nat (S n')) with (Z.of_nat (S (S n')) - 1) by lia. exact R'.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Notation POST s := (ptarget_run_post ra sp gp tpv s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB AB lo m0).
#[using="FREE p A cap INLB FC LC CAP L0 L6 SPAB CEIL LO"] Lemma run_tail : forall own st ms,
RUNST own 0x13448 0 st ms ->
implM usegs ((match omodel own with Some q => raw_free q | None => mret tt end) ;;; mret (if 0 =? 0 then 0 else 1)) st (POST st) ms.
Proof.
intros own st ms R.
destruct R as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & x19 & t3 & t4 & t5 & t6 & F & fc & m & -> & FRM & [P IV]).
pose proof IV as (FR & PB & HC & SE & [errv ERR] & MI & ST & AUX & SO & DP & AX).
pose proof facts as (PL0 & PLM & PLEN & CFG & CALLS & EPAY).
pose proof LO' as L'. pose proof CEIL as CEIL'. unfold HARNESS_STACK in CEIL', L'. atop_facts.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
pose proof (block_facts _ _ _ P) as (BA1 & BA2 & BA3 & BOWN). atop_facts.
unfold wz. destruct FR as [jb FR]. unfold RERRNO in ERR.
unfold implM. iprefix. zstep. zstep. apply evt_done.
lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm st (POST st) msx) end.
eapply implM_bind with (Q1 := fun _ st' ms' => exists (x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (errv' : word),
ms' = MS (mkR x1' SPF gp tpv t0' t1' t2' (Z_to_bv 64 plen) (Z_to_bv 64 (dptr own)) a0' a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 (oreg own)) x19 (Z_to_bv 64 PINIT_FLAG) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (-2)) s8 s9 s10 s11 t3' t4' t5' t6')
F (Z_to_bv 64 0x13450) fc None m' (seg_rom usegs)
/\ RHEAP st' LB m' /\ rw_cells usegs m' (usp + -80) [CB 8 jb; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ rw_cells usegs m' RERRNO [C4 errv'] /\ mem_inv usegs m' /\ stk usegs m' lo (usp + -80) /\ rauxv_ok m' AB
/\ stdout_file m' (ps_so st') /\ pdrv_pres LB usp m0 m' /\ atx_state true m').
{ destruct own as [[q D]|]; cbn [omodel oreg dptr LBT] in *.
-
unfold rfree_stmt in FREE.
eapply implM_mono.
{ Local Ltac2 Set LiaHints.tbl := fun () => "00N0?1048058019.94  11144297143.11911146557324.92 11472836995.13022226183811.13022840524957.94 24387450425.12126068948659.11926071145352.94 26375207947.94 27723960707.1313051486595.131 33767249679.94 35929099361.94 36925100919.94 39362997480.12042200251523.12946887021955.13250628941955.12952076332702.13153510313876.1295896867971.129 59504824357.12061994440323.13166772516082.1206936170300.120 8828204459.120 8838968076.94  8840904247.119 953052341.94   00000400500600700800900=00Q00e00f00g00h00n01401501601701801901:01;01<01=01>01?01@01A01B01C01DS2L'SSSSFS2L'S2L'5CEIL'5ATOPR3SPRS2L'5CEIL'5ATOPR3SPRFSSS4CEILS4SPABFSSSSFSSSSSSSSSF".
eapply FREE with (lo := lo) (B := AB) (p := q) (A := D) (n := plen); try reflexivity; unfold RATP;
rewrite ?(unsigned_lit 192304) by lia; rewrite ?(unsigned_lit (usp + -80)) by lia;
first [ exact P | left; reflexivity | exact AUX | lia | exact ST | exact CEIL | unfold RFREE_STACK; lia | exact ERR | exact MI ]. }
cbv beta. intros [] st' ms' PO.
destruct PO as (w0 & w1 & w2 & rb0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m3 & -> & MI3 & ST3 & ERR3 & AUX3 & HPR3 & FAE3 & SOE3 & HEAP3).
rewrite ?(unsigned_lit (usp + -80)) in ST3 by lia. rewrite ?(unsigned_lit (usp + -80)) in HPR3 by lia.
unfold RATP in ERR3. rewrite ?(unsigned_lit 192304) in ERR3 by lia. change (192304 + -164) with RERRNO in ERR3.
replace (ret_pc (Z_to_bv 64 0x13450)) with (Z_to_bv 64 0x13450) by (symmetry; rpc).
pose proof (RMalloc_ifaceP.RHEAP_blocks_nodup_proof _ _ _ P) as ND.
rewrite (lb_remove_head (q, D, plen) LB ND) in HPR3, HEAP3.
do 16 eexists. exists m3, (Z_to_bv 64 (bv_unsigned errv)).
split; [reflexivity|]. split; [exact HEAP3|].
split; [eapply rheap_pres_rw_cells; [exact HPR3| exact FR| left; cbn; lia]|].
split; [replace (Z_to_bv 64 (bv_unsigned errv)) with errv by (symmetry; apply Z_to_bv_bv_unsigned); exact ERR3|].
split; [exact MI3|]. split; [exact ST3|]. split; [exact AUX3|].
split; [rewrite SOE3; eapply stdout_file_heap_pres; [exact HPR3| exact SO]|].
split; [| eapply atx_state_heap_pres; [exact HPR3| exact AX]].
eapply pdrv_pres_trans; [exact DP|]. eapply pdrv_pres_of_heap_sub; [exact HPR3| lia| intros b Hb; exact Hb].
-
apply implM_ret. eapply evt_mono; [apply (rfree_null_spec); reflexivity|].
cbv beta. intros ms' ->. replace (ret_pc (Z_to_bv 64 0x13450)) with (Z_to_bv 64 0x13450) by (symmetry; rpc).
do 16 eexists. exists m, errv.
split; [reflexivity|]. split; [exact P|]. split; [exact FR|]. split; [exact ERR|]. split; [exact MI|]. split; [exact ST|]. split; [exact AUX|].
split; [exact SO|]. split; [exact DP| exact AX]. }
cbv beta. intros [] st' ms' (x1' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & errv' & -> & P' & FR' & ERR' & MI' & ST' & AUX' & SO' & DP' & AX').
apply implM_ret. cbn [Z.eqb].
zstep. zstep. zstep.
do 9 zstep. release_frame FR' ST' (bv_unsigned sp). zstep. zstep.
apply evt_done. unfold ptarget_run_post. do 16 eexists. exists m', errv'.
split; [reflexivity|].
split; [lia|]. split; [exact MI'|]. split; [exact FRM|]. split; [exact ST'|].
split; [unfold RATP, RERRNO in *; rewrite unsigned_lit by lia; exact ERR'|].
split; [exact AUX'|]. split; [exact DP'|]. split; [exact P'|]. split; [exact SO'| exact AX'].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition PRE1 (s : PState) (m : mem) : Prop :=
RHEAP s LB m /\ FRAME m /\ bytes_at usegs m A (zbytes content) /\ harness_cells m /\ stderr_file0 m
/\ (exists errv : word, rw_cells usegs m RERRNO [C4 errv]) /\ mem_inv usegs m /\ stk usegs m lo (usp + -80)
/\ rauxv_ok m AB /\ stdout_file m (ps_so s) /\ pdrv_pres LB usp m0 m /\ atx_state true m.
Notation EST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x22 x23 t3 t4 t5 t6 F fc mm :=
(MS (mkR x1 SPF gp tpv t0 t1 t2 (Z_to_bv 64 plen) x9 a0 a1 a2 a3 a4 a5 a6 a7
x18 x19 (Z_to_bv 64 PINIT_FLAG) (Z_to_bv 64 calls) x22 x23 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
#[using="FREE FUZZ EMIT FWXO p cap INLB FC LC CAP L0 L6 SPAB ABB SP16 CEIL LO"] Lemma trun_empty : forall s x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x22 x23 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (m : mem),
plen = 0 -> frm0 fc -> PRE1 s m ->
implM usegs (Prog.run cfg payload) s (POST s) (EST 0x13400 x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x22 x23 t3 t4 t5 t6 F fc m).
Proof.
intros until m. intros PZ FRM (P & FR & CT & HC & SE & [errv ERR] & MI & ST & AUX & SO & DP & AX).
pose proof facts as (PL0 & PLM & PLEN & CFG & CALLS & EPAY).
unfold Prog.run, Adapter.target_run. rewrite PLEN. replace (plen =? 0) with true by (symmetry; apply Z.eqb_eq; exact PZ).
change (1 + Z.land cfg 3) with calls.
apply implM_retb. cbv beta iota.
unfold implM. iprefix. zstep. zstep. zstep. zstep. apply evt_done.
lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s (POST s) msx) end.
eapply implM_bind.
{ Local Ltac2 Set LiaHints.tbl := fun () => "0040>13168177946.8820902611171.8851311406230.8854684131344.8900000700>00E00FS5CALLSS2L02PZS5CALLSS".
eapply (calls_loop (Z.to_nat calls) None 0); [lia| exact PZ|].
unfold RUNST. do 17 eexists. exists F, fc, m. rewrite Z2Nat.id by lia.
split; [cbn [dptr oreg]; unfold PEMPTY, PINIT_FLAG, wz; reflexivity|].
split; [exact FRM|]. split; [exact P|].
split; [exact FR|].
assert (PE : payload = []). { unfold payload. apply skipn_all2. unfold plen, zlength in PZ. lia. }
split; [cbn [dptr]; rewrite PE; cbn [zbytes map]; apply bytes_at_nil; unfold PEMPTY; lia|].
split; [exact HC|]. split; [exact SE|]. split; [exists errv; exact ERR|]. split; [exact MI|]. split; [exact ST|]. split; [exact AUX|]. split; [exact SO|]. split; [exact DP| exact AX]. }
cbv beta. intros rc st' ms' [R ->]. apply (run_tail None st' ms' R).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="lo SP16 CEIL LO"] Lemma pdrv_pres_of_newblock : forall st q D n m m',
RHEAP st ((q, D, n) :: LB) m -> munch [(D, D + n)] m m' -> wmono usegs m m' -> pdrv_pres LB usp m m'.
Proof.
intros st q D n m m' P MU WM a Ha Hc Hx.
destruct (magree_of_munch usegs _ _ _ MU WM a Ha) as [E V]; [| split; [exact E| exact V]].
cbn. split; [| exact I].
pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ (q, D, n) P ltac:(left; reflexivity)) as (B1 & B2 & B3 & B4 & B5). cbn in B1, B2, B3, B4, B5.
pose proof LO' as L'. pose proof CEIL as CEIL'. unfold HARNESS_STACK in CEIL', L', B4. atop_facts.
Local Ltac2 Set LiaHints.tbl := fun () => "0020>31460369227.6231470708830.6900000C00JS2Hc2B42L'5CEIL'2B5S2Hr2DJ".
destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [lia| unfold ralloc_static in Hc; lia|].
pose proof (RMalloc_ifaceP.RHEAP_blocks_nodup_proof _ _ _ P) as ND.
pose proof (RMalloc_ifaceP.RHEAP_blocks_disjoint_proof _ _ _ (q, D, n) b P ltac:(left; reflexivity) ltac:(right; exact Hb)) as DJ.
cbn [blk_id blk_addr blk_size fst snd] in DJ.
assert (NE : q <> blk_id b).
{ cbn [map blk_id fst] in ND. apply NoDup_cons_iff in ND. destruct ND as [NI _]. intros E. apply NI. rewrite E. apply in_map. exact Hb. }
specialize (DJ NE). destruct b as [[bi ba] bs]. cbn [blk_addr blk_size blk_id fst snd] in DJ, Hr. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="MALLOC FREE FUZZ EMIT FWXO p cap INLB FC LC CAP L0 L6 SPAB ABB SP16 CEIL LO"] Lemma trun_copy : forall s x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x22 x23 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (m : mem),
plen <> 0 -> frm0 fc -> PRE1 s m ->
implM usegs (Prog.run cfg payload) s (POST s) (EST 0x133b4 x1 t0 t1 t2 (Z_to_bv 64 PAY) a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x22 x23 t3 t4 t5 t6 F fc m).
Proof.
intros until m. intros PZ FRM (P & FR & CT & HC & SE & [errv ERR] & MI & ST & AUX & SO & DP & AX).
pose proof facts as (PL0 & PLM & PLEN & CFG & CALLS & EPAY).
pose proof LO' as L'. pose proof CEIL as CEIL'. unfold HARNESS_STACK in CEIL', L'. atop_facts.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
pose proof (block_facts s None m P) as (BA1 & BA2 & BA3 & _). atop_facts.
pose proof (bytes_at_bound _ _ _ _ CT) as CTB. rewrite zbytes_length in CTB.
assert (PLEN' : Z.of_nat (length payload) = plen) by (unfold zlength in PLEN; exact PLEN).
unfold zlength in LC, L6.
unfold Prog.run, Adapter.target_run. rewrite !PLEN.
replace (plen =? 0) with false by (symmetry; apply Z.eqb_neq; exact PZ).
change (1 + Z.land cfg 3) with calls.
apply implM_bind_assoc.
destruct FR as [jb FR]. unfold RERRNO in ERR.
unfold implM. iprefix. zstep. zstep. apply evt_done.
lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s (POST s) msx) end.
eapply implM_bind.
{ unfold rmalloc_stmt in MALLOC.
Local Ltac2 Set LiaHints.tbl := fun () => "00i0?1046255492.96  10861763953.15511472836995.13213155463354.15315124359297.13715774275062.15618507461255.15418759263454.15419386403565.13721488469769.15421706042413.13822226183811.13322706553362.15722838136762.96 24249284766.12424374289723.96 24389370787.12525019308679.15326058300948.12326068817071.96 26377007916.96 27723960707.13327839242640.12330099201811.1373051486595.133 32977115099.15733764923432.96 35369668685.15535931423558.96 36923300944.96 37188910021.15837188910021.15938450586863.15338689953943.15639362537470.12342200251523.13346887021955.13450628941955.13351313222918.13751315732278.15356219159088.1535896867971.132 59308628304.13859504824383.12460967875283.13761994440323.13464409705683.15665172888733.13665904326393.15367009794312.1246933890827.124 6934087340.156 8826123920.123 8828204465.124 8840772651.96  954917778.96   9571950299.157 00000400500600E00V00W00X00f01501601O01P01T01U01Y01b01f01k02?02S02T02U02V02i02j02k03103203803903S03[03\04904:04;04<04=04B04I04J04K04S04T04_04`04a04h05305405505605705805905:05;S2L'FSS5CALLS3SPR3BQ1S2LC2L04EPAY4DISJFFS2L'5CEIL'3BQ4S3SPR5PLEN'3BQ1FS5ATOPR3SPR5PLEN'3BQ13BQ4SS2HaFS2LCS3PL03PLMS2L'S3BQ5S2L'5CEIL'5ATOPR3SPRS2L'5CEIL'5ATOPR3SPRFSSS2LC4EPAY5ATOPR3BA2SSS4CEILFS4SPABFS3BQ52Ha2LC2L02L63BA34DISJS3BQ52HaSS4SPAB2L'5CEIL'5ATOPR3BQ43BQ5SSSSS3PL0S5CALLSSSS3BQ12K1SS5ATOPR3BQ4SFS2L02L6S5CEIL'3BQ4SSSSSSFS".
eapply MALLOC with (lo := lo) (B := AB); try reflexivity; unfold RATP; rewrite ?(unsigned_lit 192304) by lia; rewrite ?(unsigned_lit (usp + -80)) by lia;
first [ exact P | exact AUX | lia | exact ST | exact CEIL | unfold RMALLOC_STACK; lia | exact ERR | exact MI ]. }
cbv beta. intros r s1' ms1 PO.
destruct PO as (u0 & u1 & u2 & ra0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & errv1 & -> & MI1 & ST1 & ERR1 & AUX1 & HPR & FAE & SOE & RR).
unfold RATP in ERR1. rewrite ?(unsigned_lit 192304) in ERR1 by lia. rewrite ?(unsigned_lit (usp + -80)) in ST1 by lia. rewrite ?(unsigned_lit (usp + -80)) in HPR by lia.
change (192304 + -164) with 192140 in ERR1.
replace (ret_pc (Z_to_bv 64 0x133bc)) with (Z_to_bv 64 0x133bc) by (symmetry; rpc).
assert (FR1 : rw_cells usegs m1 (usp + -80) [CB 8 jb; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) by (eapply rheap_pres_rw_cells; [exact HPR| exact FR| left; cbn; lia]).
assert (CT1 : bytes_at usegs m1 A (zbytes content)).
{ eapply rheap_pres_bytes_at; [exact HPR| exact CT|]. right; right. exists (p, A, cap). split; [exact INLB|]. cbn. rewrite zbytes_length. lia. }
assert (AX1 : atx_state true m1) by (eapply atx_state_heap_pres; [exact HPR| exact AX]).
destruct r as [nb|].
2:{
destruct RR as [-> HEAP1].
apply implM_retb. cbv beta iota. apply implM_ret.
zstep. if_cases K1; zify_cond K1; [| exfalso; apply K1; reflexivity].
zstep. zstep. do 9 zstep. release_frame FR1 ST1 (bv_unsigned sp). zstep. zstep.
apply evt_done. unfold ptarget_run_post. do 16 eexists. exists m1, errv1.
split; [reflexivity|]. split; [lia|]. split; [exact MI1|]. split; [exact FRM|]. split; [exact ST1|].
split; [unfold RATP, RERRNO in *; rewrite unsigned_lit by lia; exact ERR1|].
split; [exact AUX1|].
split; [eapply pdrv_pres_trans; [exact DP| eapply pdrv_pres_of_heap_sub; [exact HPR| lia| intros b Hb; exact Hb]]|].
split; [exact HEAP1|]. split; [rewrite SOE; eapply stdout_file_heap_pres; [exact HPR| exact SO]| exact AX1]. }
destruct RR as (A' & junk' & -> & BR' & HEAP1 & NBLK & _).
pose proof BR' as (BQ1 & BQ2 & BQ3 & BQ4 & BQ5). atop_facts.
pose proof (RMalloc_ifaceP.RHEAP_blocks_nodup_proof _ _ _ HEAP1) as ND.
assert (DISJ : A' + plen <= A \/ A + cap <= A').
{ pose proof (RMalloc_ifaceP.RHEAP_blocks_disjoint_proof _ _ _ (nb, A', plen) (p, A, cap) HEAP1 ltac:(left; reflexivity) ltac:(right; exact INLB)) as D.
cbn [blk_id blk_addr blk_size fst snd] in D. apply D. cbn [map blk_id fst] in ND. apply NoDup_cons_iff in ND. destruct ND as [NI _]. intros E. apply NI. rewrite E.
apply (in_map blk_id) in INLB. exact INLB. }
assert (PB : bytes_at usegs m1 PAY (zbytes payload)).
{ rewrite <- (firstn_skipn (Z.to_nat (6 + L)) (zbytes content)) in CT1. apply bytes_at_app in CT1. destruct CT1 as [_ X].
rewrite length_firstn, zbytes_length in X. unfold payload, zbytes. rewrite <- skipn_map. unfold zbytes in X.
replace (A + Z.of_nat (Nat.min (Z.to_nat (6 + L)) (length content))) with PAY in X by (rewrite EPAY; lia). exact X. }
apply implM_retb. cbv beta iota.
unfold implM. iprefix.
zstep. if_cases K1; zify_cond K1; [exfalso; rewrite ?unsigned_lit in K1 by lia; lia|]. clear K1.
zstep. zstep. zstep. zstep.
eapply evt_cut.
{ eapply memcpy_callv with (src := zbytes payload) (junk := junk');
[exact PB| rewrite zbytes_length; lia| exact NBLK| unfold plen, zlength in *; lia| lia| unfold plen, zlength in *; lia| lia| exact MI1]. }
cbv beta. intros ms' PO.
destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & -> & MUc & WMc & MI2 & NB2 & _).
transport_after_call usegs m1 m2 MUc WMc.
replace (ret_pc (Z_to_bv 64 0x133d0)) with (Z_to_bv 64 0x133d0) by (symmetry; rpc).
assert (P2 : RHEAP s1' ((nb, A', plen) :: LB) m2).
{ eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact HEAP1| exact MUc| exact WMc|].
constructor; [| constructor]. right; right. exists (nb, A', plen). split; [left; reflexivity|]. cbn. lia. }
pose proof (magree_of_munch usegs _ _ _ MUc WMc) as AG.
assert (OUT : forall a, (a < A' \/ A' + plen <= a) -> (fun a0 : Z => outside [(A', A' + plen)] a0) a) by (intros a Ha; cbn; lia).
assert (IV2 : INV0 (Some (nb, A')) s1' m2).
{ split; [exists jb; exact FR1|].
split; [cbn [dptr]; apply (rw_cells_bytes_at usegs) in NB2; cbn [cells_bytes cbytes app] in NB2; rewrite app_nil_r in NB2; exact NB2|].
split. { destruct HC as (C5 & C6). unfold harness_cells, PGOT_STDERR, PSTDERR_PTR in *.
Ltac hq HPR AG OUT C := eapply rw_cells_magree; [exact AG| eapply rheap_pres_rw_cells; [exact HPR| exact C| right; left; cbn; unfold RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP; lia]| intros a Ha; apply OUT; cbn in Ha; lia].
split; [hq HPR AG OUT C5| hq HPR AG OUT C6]. }
split. { eapply (stderr_file0_agree _ _ _ AG); [intros a Ha; apply OUT; unfold stderr_addr in Ha; lia|]. eapply stderr_file0_heap_pres; [exact HPR| exact SE]. }
split; [exists errv1; exact ERR1|]. split; [exact MI2|]. split; [exact ST1|].
split. { eapply rauxv_ok_frame; [exact AUX1| exact MUc| exact WMc|]. unfold RAUXV_CELL, RLIBC in *. constructor; [cbn [fst snd]; lia| constructor]. }
split. { rewrite SOE. eapply (stdout_file_agree _ _ _ _ AG); [intros a Ha; apply OUT; unfold stdout_addr in Ha; lia|]. eapply stdout_file_heap_pres; [exact HPR| exact SO]. }
split. { eapply pdrv_pres_trans; [exact DP|]. eapply pdrv_pres_trans; [eapply pdrv_pres_of_heap_sub; [exact HPR| lia| intros b Hb; exact Hb]|].
eapply pdrv_pres_of_newblock; [exact HEAP1| exact MUc| exact WMc]. }
eapply (atx_state_agree _ _ _ _ AG); [| exact AX1]. intros a Ha. apply OUT. unfold atx_state_addr, atx_addr, PATX, PAEF_INCB in Ha. lia. }
clear AG OUT MUc WMc.
zstep. zstep. zstep. zstep. apply evt_done.
lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s1' (POST s1') msx) end || idtac.
lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s1' (POST s) msx) end || idtac.
eapply implM_bind.
{ eapply (calls_loop (Z.to_nat calls) (Some (nb, A')) 0); [lia| exact I|].
unfold RUNST. do 17 eexists. exists F, fc, m2. rewrite Z2Nat.id by lia.
split; [cbn [dptr oreg]; unfold PINIT_FLAG, wz; reflexivity|].
split; [exact FRM|]. split; [exact P2| exact IV2]. }
cbv beta. intros rc st' ms'' [R ->]. apply (run_tail (Some (nb, A')) st' ms'' R).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="MALLOC FREE FUZZ EMIT FWXO p cap INLB FC LC CAP L0 L6 SPAB ABB SP16 CEIL LO"] Lemma trun_main : forall (tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (s : PState) (errv : word),
RHEAP s LB m0 -> bytes_at usegs m0 A (zbytes content) -> trun_cells0 m0 -> stderr_file0 m0 -> rauxv_ok m0 AB ->
stk usegs m0 lo usp -> rw_cells usegs m0 RERRNO [C4 errv] -> mem_inv usegs m0 -> frm0 fc ->
stdout_file m0 (ps_so s) ->
tp = tpv -> a0 = Z_to_bv 64 (A + 2) -> a1 = Z_to_bv 64 L -> a2 = Z_to_bv 64 PAY -> a3 = Z_to_bv 64 plen ->
implM usegs (Prog.run cfg payload) s (POST s)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 PTARGET_RUN) fc None m0 (seg_rom usegs)).
Proof.
intros until errv. intros P0 CT TR0 SE0 AUX0 ST0 ERR0 MI0 FRM SO0 -> -> -> -> ->.
pose proof facts as (PL0 & PLM & PLEN & CFG & CALLS & EPAY).
pose proof LO' as L'. pose proof CEIL as CEIL'. unfold HARNESS_STACK in CEIL', L'. atop_facts.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
pose proof (block_facts s None m0 P0) as (BA1 & BA2 & BA3 & _). atop_facts.
pose proof (bytes_at_bound _ _ _ _ CT) as CTB. rewrite zbytes_length in CTB.
assert (PLEN' : Z.of_nat (length payload) = plen) by (unfold zlength in PLEN; exact PLEN).
unfold zlength in LC, L6. unfold RERRNO in ERR0.
unfold implM. eapply impl_evt; [| intros ms' H; exact H].
eapply trun_init; [exact ST0| exact MI0| exact TR0| exact (RHEAP_need_locks _ _ _ P0)|].
intros m1 x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 FR ST1 HC1 AX1 MU WM MI1.
unfold PINIT_FLAG, PATX in MU.
pose proof (magree_of_munch usegs _ _ _ MU WM) as AG.
assert (OUT : forall a, ((a < lo /\ (a < 0x10000 \/ 0x50000 <= a)) \/ (0x10000 <= a < 0x50000 /\ ~ (0x2ee30 <= a < 0x2ee30 + 1) /\ ~ (0x4ef78 <= a < 0x4f0a0)))
-> (fun a0 : Z => outside [(usp - 128, usp); (0x2ee30, 0x2ee30 + 1); (0x4ef80, 0x4ef84); (0x4ef88, 0x4ef90); (0x4ef98, 0x4efa0); (0x4f098, 0x4f0a0)] a0) a).
{ intros a Ha. cbn. Local Ltac2 Set LiaHints.tbl := fun () => "00Q0?10522004024.10512751668790.10212805561706.11114314637994.11117325686075.11018603286075.11018633903475.11219084401088.11021552856444.11123018893550.10224434346666.11124480245911.1062524670392.106 31474779266.10431474779266.10735559555610.10435559555610.10736346138695.10837058088418.10437058088418.10738070439215.11041418171244.10548756605499.11058784830011.11059310760529.10360543471717.10662127590522.10962127590522.11062127590522.11163372904650.11163922334890.1117453863398.106 8806420828.107 00000700;00<00=00R00g01101F01G01U01V01[01^01g02002802F02e02m03503J03K03`04504@04D04H04L04P04Z04[04\04oS2L02KLS2KLSSS4SPAB2L'5CEIL'5ATOPRS4SPAB2L'5CEIL'5ATOPRS2L'5CEIL'S4SPAB2L'5CEIL'5ATOPRSS2LC3CAP2L02L6SS3C2RS1HS3PL03PLMS3PL03PLMS3PL02KPS2L03PL02KL2KPS2LC5CEIL'5ATOPR3SPR3BA23BA32HaS3PL02KPS3PL02KPS4SPAB2L'5CEIL'5ATOPRSS4SPAB2L'5CEIL'5ATOPRS4SPAB2L'5CEIL'5ATOPRS2L02L63EC2S2ECS2HaS2HaS2HaS2L'5CEIL'SSS2L'5CEIL'5ATOPR2Ha".
lia. }
assert (CT1 : bytes_at usegs m1 A (zbytes content)).
{ eapply bytes_at_magree; [exact AG| exact CT|]. intros a Ha. apply OUT. left. rewrite zbytes_length in Ha. lia. }
assert (ERR1 : rw_cells usegs m1 RERRNO [C4 errv]).
{ eapply rw_cells_magree; [exact AG| exact ERR0|]. intros a Ha. apply OUT. right. unfold RERRNO in *. cbn in Ha. lia. }
assert (SE1 : stderr_file0 m1) by (eapply (stderr_file0_agree _ _ _ AG); [| exact SE0]; intros a Ha; apply OUT; right; unfold stderr_addr in Ha; lia).
assert (SO1 : stdout_file m1 (ps_so s)) by (eapply (stdout_file_agree _ _ _ _ AG); [| exact SO0]; intros a Ha; apply OUT; right; unfold stdout_addr in Ha; lia).
assert (AUX1 : rauxv_ok m1 AB).
{ eapply rauxv_ok_frame; [exact AUX0| exact MU| exact WM|]. unfold RAUXV_CELL, RLIBC in *.
repeat (constructor; [cbn [fst snd]; lia|]). constructor. }
assert (P1 : RHEAP s LB m1).
{ eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact P0| exact MU| exact WM|].
constructor; [left; cbn [fst snd]; atop_facts; lia|].
repeat (constructor; [right; left; cbn [fst snd]; unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP; lia|]). constructor. }
assert (DP1 : pdrv_pres LB usp m0 m1).
{ eapply pdrv_pres_of_munch; [exact MU| exact WM| | apply (LB_below s None m0 P0)].
constructor; [left; cbn [fst snd]; lia|].
unfold pstdout_ivs, PINIT_FLAG, PAEF_INCB, PATX.
repeat (constructor; [right; cbn; tauto|]). constructor. }
assert (PRE : PRE1 s m1).
{ split; [exact P1|]. split; [exact FR|]. split; [exact CT1|]. split; [exact HC1|]. split; [exact SE1|]. split; [exists errv; exact ERR1|].
split; [exact MI1|]. split; [exact ST1|]. split; [exact AUX1|]. split; [exact SO1|]. split; [exact DP1| exact AX1]. }
clear AG OUT MU WM CT ERR0 SE0 SO0 AUX0 P0 ST0 MI0 TR0.
zstep. if_cases KL; zify_cond KL.
-
assert (EC : calls = 1) by (unfold calls, cfg; replace (0 <? L) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
zstep. zstep. if_cases KP; zify_cond KP.
+
apply evt_done. rewrite <- EC.
eapply trun_copy; [rewrite ?unsigned_lit in KP by lia; lia| exact FRM| exact PRE].
+ apply evt_done. rewrite <- EC.
eapply trun_empty; [rewrite ?unsigned_lit in KP by lia; lia| exact FRM| exact PRE].
-
destruct (nth_error content 2) as [c2|] eqn:EC2; [| exfalso; apply nth_error_None in EC2; lia].
pose proof (proj1 (Forall_forall _ _) FC c2 (nth_error_In _ _ EC2)) as C2R. cbn beta in C2R.
pose proof (u8ro_read usegs m1 A (zbytes content) 2 (Z_to_bv 8 c2) (Z_to_bv 64 (A + 2)) CT1 ltac:(unfold zbytes; rewrite nth_error_map, EC2; reflexivity) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
zstep. clear RD.
zstep. zstep.
assert (EC : calls = Z.land c2 3 + 1).
{ unfold calls, cfg. replace (0 <? L) with true by (symmetry; apply Z.ltb_lt; lia). unfold znth.
destruct (Z.ltb_spec 2 0); [lia|]. change (Z.to_nat 2) with 2%nat. rewrite (nth_error_nth _ _ _ EC2). lia. }
replace (bv_unsigned (Z_to_bv 8 c2)) with c2
by (rewrite Z_to_bv_unsigned; unfold bv_wrap; symmetry; apply Z.mod_small; unfold bv_modulus; cbn; lia).
replace (Z.land c2 3 + 1) with calls by lia.
zstep. if_cases KP; zify_cond KP.
+ apply evt_done. eapply trun_empty; [rewrite ?unsigned_lit in KP by lia; lia| exact FRM| exact PRE].
+ apply evt_done. eapply trun_copy; [rewrite ?unsigned_lit in KP by lia; lia| exact FRM| exact PRE].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End RUN.
#[using="Type"] Theorem ptarget_run_proof :
rmalloc_stmt -> rfree_stmt -> fuzz_one_stmt -> emit_printf_stmt ps_so set_so_ps -> fwritex_stdout_stmt ->
ptarget_run_stmt.
Proof.
intros MALLOC FREE FUZZ EMIT FWXO.
intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A cap L content AB lo errv.
intros P0 INLB CT FC LC CAP L0 L6 TR0 SE0 AUX0 SPAB ABB ST0 CEIL LO ERR0 MI0 FRM SO0 -> SP16 -> -> -> ->.
eapply (trun_main MALLOC FREE FUZZ EMIT FWXO ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m LB p A cap L content AB lo
INLB FC LC CAP L0 L6 SPAB ABB SP16 CEIL LO);
[exact P0| exact CT| exact TR0| exact SE0| exact AUX0| exact ST0| | exact MI0| exact FRM| exact SO0| reflexivity| reflexivity| reflexivity| unfold PAY; reflexivity| unfold plen; reflexivity].
unfold RATP, RERRNO, wz in ERR0 |- *. Local Ltac2 Set LiaHints.tbl := fun () => "0010=8841017104.67000001S".
rewrite (unsigned_lit 192304) in ERR0 by lia. exact ERR0.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
